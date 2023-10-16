use std::marker::PhantomData;

use halo2_proofs::{arithmetic::Field, circuit::*, plonk::*, poly::Rotation};

use crate::is_zero::{IsZeroChip, IsZeroConfig};

#[derive(Clone, Debug)]
pub struct FactorConfig<F: Field> {
    lhs: Column<Advice>,
    rhs: Column<Advice>,
    mul: Column<Advice>,
    instance: Column<Instance>,
    lhs_equals_one: IsZeroConfig<F>,
    rhs_equals_one: IsZeroConfig<F>,
    selector: Selector,
}
#[derive(Debug, Clone)]
struct FactorChip<F: Field> {
    config: FactorConfig<F>,
    _marker: PhantomData<F>,
}

impl<F: Field> FactorChip<F> {
    pub fn construct(config: FactorConfig<F>) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> FactorConfig<F> {
        let lhs = meta.advice_column();
        let rhs = meta.advice_column();
        let mul = meta.advice_column();
        let instance = meta.instance_column();
        let selector = meta.selector();

        let lhs_inv = meta.advice_column();
        let lhs_equals_one = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(selector),
            |meta| meta.query_advice(lhs, Rotation::cur()) - Expression::Constant(F::ONE),
            lhs_inv,
        );

        let rhs_inv = meta.advice_column();
        let rhs_equals_one = IsZeroChip::configure(
            meta,
            |meta| meta.query_selector(selector),
            |meta| meta.query_advice(rhs, Rotation::cur()) - Expression::Constant(F::ONE),
            rhs_inv,
        );

        meta.enable_equality(mul);
        meta.enable_equality(instance);

        meta.create_gate("Mul & NotEqOne Gate", |meta| {
            let s = meta.query_selector(selector);
            let l = meta.query_advice(lhs, Rotation::cur());
            let r = meta.query_advice(rhs, Rotation::cur());
            let m = meta.query_advice(mul, Rotation::cur());
            vec![
                s.clone() * (l * r - m),
                s.clone() * lhs_equals_one.expr(),
                s * rhs_equals_one.expr(),
            ]
        });

        FactorConfig {
            lhs,
            rhs,
            mul,
            instance,
            lhs_equals_one,
            rhs_equals_one,
            selector,
        }
    }

    pub fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        lhs: F,
        rhs: F,
    ) -> Result<AssignedCell<F, F>, Error> {
        let lhs_equals_one = IsZeroChip::construct(self.config.lhs_equals_one.clone());
        let rhs_equals_one = IsZeroChip::construct(self.config.rhs_equals_one.clone());

        layouter.assign_region(
            || "Factor circuit assign",
            |mut region| {
                self.config.selector.enable(&mut region, 0)?;

                let lhs_cell =
                    region.assign_advice(|| "lhs", self.config.lhs, 0, || Value::known(lhs))?;
                let rhs_cell =
                    region.assign_advice(|| "rhs", self.config.rhs, 0, || Value::known(rhs))?;
                let mul_cell = region.assign_advice(
                    || "mul",
                    self.config.mul,
                    0,
                    || lhs_cell.value().copied() * rhs_cell.value(),
                )?;
                lhs_equals_one.assign(&mut region, 0, Value::known(lhs - F::ONE))?;
                rhs_equals_one.assign(&mut region, 0, Value::known(rhs - F::ONE))?;

                Ok(mul_cell)
            },
        )
    }

    pub fn expose_public(
        &self,
        mut layouter: impl Layouter<F>,
        cell: &AssignedCell<F, F>,
        row: usize,
    ) -> Result<(), Error> {
        layouter.constrain_instance(cell.cell(), self.config.instance, row)
    }
}

#[derive(Default)]
pub struct FactorCircuit<F: Field> {
    pub lhs: F,
    pub rhs: F,
}

impl<F: Field> Circuit<F> for FactorCircuit<F> {
    type Config = FactorConfig<F>;
    type FloorPlanner = SimpleFloorPlanner;

    fn without_witnesses(&self) -> Self {
        Self::default()
    }

    fn configure(meta: &mut ConstraintSystem<F>) -> Self::Config {
        FactorChip::configure(meta)
    }

    fn synthesize(
        &self,
        config: Self::Config,
        mut layouter: impl Layouter<F>,
    ) -> Result<(), Error> {
        let chip = FactorChip::construct(config);

        let mul_cell =
            chip.assign_row(layouter.namespace(|| "circuit assign"), self.lhs, self.rhs)?;

        chip.expose_public(layouter.namespace(|| "expose"), &mul_cell, 0)?;

        Ok(())
    }
}

#[cfg(test)]
mod tests {
    use super::FactorCircuit;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::Fr as Fp;

    #[test]
    fn innocent_prover() {
        let k = 4;
        let lhs = Fp::from(11);
        let rhs = Fp::from(13);
        let circuit = FactorCircuit { lhs, rhs };
        let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(143)]]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn malicious_prover() {
        let k = 4;
        let lhs = Fp::from(1);
        let rhs = Fp::from(143);
        let circuit = FactorCircuit { lhs, rhs };
        let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(143)]]).unwrap();
        prover.assert_satisfied();
    }
}
