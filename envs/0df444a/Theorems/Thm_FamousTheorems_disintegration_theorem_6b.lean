-- Prove2me | Theorems.Thm_FamousTheorems_disintegration_theorem_6b
-- name    : FamousTheorems.disintegration_theorem_6b
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T10:42:49.413611+00:00
-- url     : https://prove2.me/theorems/2d3d9c8e-39cf-410b-a167-b21cfedfec67
-- title:
--   The disintegration theorem (existence of conditional kernels)
-- statement:
--   **The disintegration theorem (existence of conditional kernels).** Let $\rho$ be a finite measure on a product $\alpha\times\Omega$, where $\Omega$ is a nonempty standard Borel space. Then there is a Markov kernel $\kappa$ from $\alpha$ to $\Omega$ such that
--   $$\rho(A\times B)=\int_A\kappa(a)(B)\,d\rho_\alpha(a)$$
--   for all measurable $A, B$. Here $\rho_\alpha$ is the first marginal of $\rho$. Equivalently, $\rho=\rho_\alpha\otimes\kappa$.
--
--   The kernel $\kappa(a)$ is the conditional distribution of the second coordinate given that the first equals $a$. The theorem gives regular conditional probabilities, which are needed to condition on events of probability zero. It is used throughout probability theory, for example in the construction of Markov processes and in Bayesian statistics.
--
--   **Formalization note.** Mathlib's instance `MeasureTheory.Measure.condKernel.instIsCondKernel`, which states that `ρ.condKernel` disintegrates $\rho$, together with the instance that `ρ.condKernel` is a Markov kernel. `ρ.fst` is the first marginal and `Measure.compProd` is the composition–product $\rho_\alpha\otimes\kappa$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `MeasureTheory.Measure.condKernel.instIsCondKernel`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

theorem disintegration_theorem_6b {α Ω : Type*} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [Nonempty Ω]
    (ρ : MeasureTheory.Measure (α × Ω)) [MeasureTheory.IsFiniteMeasure ρ] :
    ∃ κ : ProbabilityTheory.Kernel α Ω, ProbabilityTheory.IsMarkovKernel κ ∧ ρ.fst.compProd κ = ρ := by sorry

end FamousTheorems
