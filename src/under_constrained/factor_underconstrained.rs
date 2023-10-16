use std::marker::PhantomData;

use halo2_proofs::{arithmetic::Field, circuit::*, plonk::*, poly::Rotation};

#[derive(Clone, Debug)]
pub struct FactorConfig {
    lhs: Column<Advice>,
    rhs: Column<Advice>,
    mul: Column<Advice>,
    instance: Column<Instance>,
    selector: Selector,
}
#[derive(Debug, Clone)]
struct FactorChip<F: Field> {
    config: FactorConfig,
    _marker: PhantomData<F>,
}

impl<F: Field> FactorChip<F> {
    pub fn construct(config: FactorConfig) -> Self {
        Self {
            config,
            _marker: PhantomData,
        }
    }

    pub fn configure(meta: &mut ConstraintSystem<F>) -> FactorConfig {
        let lhs = meta.advice_column();
        let rhs = meta.advice_column();
        let mul = meta.advice_column();
        let instance = meta.instance_column();
        let selector = meta.selector();

        meta.enable_equality(mul);
        meta.enable_equality(instance);

        meta.create_gate("Mul Gate", |meta| {
            let s = meta.query_selector(selector);
            let l = meta.query_advice(lhs, Rotation::cur());
            let r = meta.query_advice(rhs, Rotation::cur());
            let m = meta.query_advice(mul, Rotation::cur());
            vec![s * (l * r - m)]
        });

        FactorConfig {
            lhs,
            rhs,
            mul,
            instance,
            selector,
        }
    }

    pub fn assign_row(
        &self,
        mut layouter: impl Layouter<F>,
        lhs: Value<F>,
        rhs: Value<F>,
    ) -> Result<AssignedCell<F, F>, Error> {
        layouter.assign_region(
            || "Factor circuit assign",
            |mut region| {
                let lhs_cell = region.assign_advice(|| "lhs", self.config.lhs, 0, || lhs)?;
                let rhs_cell = region.assign_advice(|| "rhs", self.config.rhs, 0, || rhs)?;
                let mul_cell = region.assign_advice(
                    || "mul",
                    self.config.mul,
                    0,
                    || lhs_cell.value().copied() * rhs_cell.value(),
                )?;
                self.config.selector.enable(&mut region, 0)?;

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
    pub lhs: Value<F>,
    pub rhs: Value<F>,
}

impl<F: Field> Circuit<F> for FactorCircuit<F> {
    type Config = FactorConfig;
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
    use halo2_proofs::circuit::Value;
    use halo2_proofs::dev::MockProver;
    use halo2_proofs::halo2curves::bn256::Fr as Fp;

    #[test]
    fn innocent_prover() {
        let k = 4;
        let lhs = Value::known(Fp::from(11));
        let rhs = Value::known(Fp::from(13));
        let circuit = FactorCircuit { lhs, rhs };
        let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(143)]]).unwrap();
        prover.assert_satisfied();
    }

    #[test]
    fn malicious_prover() {
        let k = 4;
        let lhs = Value::known(Fp::from(1));
        let rhs = Value::known(Fp::from(143));
        let circuit = FactorCircuit { lhs, rhs };
        let prover = MockProver::run(k, &circuit, vec![vec![Fp::from(143)]]).unwrap();
        prover.assert_satisfied();
    }
}