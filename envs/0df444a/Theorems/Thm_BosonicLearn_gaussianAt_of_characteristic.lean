-- Prove2me | Theorems.Thm_BosonicLearn_gaussianAt_of_characteristic
-- name    : BosonicLearn.gaussianAt_of_characteristic
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T20:38:00.202323+00:00
-- url     : https://prove2.me/theorems/668b6bb2-fa8a-4115-8277-dca716abd4ad
-- title:
--   A state with Gaussian characteristic function $\exp(-\tfrac14\xi^T\gamma\xi+i\xi\cdot d)$ is a Gaussian state
-- statement:
--   The auxiliary clauses of the definition of a Gaussian state are automatic.
--
--   Let $\rho$ be a state on the $n$-mode Fock space whose characteristic function is
--
--   $$
--   \operatorname{Tr}\big(\rho\,e^{i\xi\cdot\hat r}\big)=\exp\!\big(-\tfrac14\,\xi^T\gamma\,\xi+i\,\xi\cdot d\big)\qquad(\xi\in\mathbb R^{2n})
--   $$
--
--   for a symmetric real matrix $\gamma$ and a vector $d$. Then $\rho$ has finite mean photon number, the series defining its characteristic function converge, and its first and second moments are $d$ and $\gamma$: all clauses of the published predicate `GaussianAt ρ d γ` hold.
--
--   Role. `IsGaussianState ρ μ Σ` is `GaussianAt` with $\gamma=2\Sigma$; this lemma reduces it to the characteristic function identity, so that states built by displacement or Gaussian mixing are recognized as Gaussian (`BosonicLearn.gaussianState_exists_of_le`).
--
--   **Formalization Note** `GaussianAt` and `CompleteMoments` are the published predicates of `Support50.P14` (interleaved quadrature coordinates).
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, Eqs. (2) and (4), pp. 4–5 (Gaussian states, displacement operators, characteristic function)

import Mathlib
import Definitions.Def_BosonicLearn_husimiQ
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open MeasureTheory
open scoped ENNReal

namespace BosonicLearn

/-- **A state with a Gaussian characteristic function is a Gaussian state.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, Eqs. (2) and (4), pp. 4–5: "A Gaussian state is a state whose Wigner function is a Gaussian distribution … Such a state
is completely determined by its first and second moments".

Let `ρ` be a state whose characteristic function is `Tr(ρ e^{iξ·r̂}) = exp(−¼ ξᵀγξ + i ξ·d)` for a symmetric real
matrix `γ` and a vector `d`. Then `ρ` satisfies all clauses of the published predicate `GaussianAt ρ d γ`: finite mean
photon number, convergence of the characteristic series, and the first and second moment identities.

**Formalization Note.** `GaussianAt` (`Support50.P14`) is the predicate behind `IsGaussianState`; this lemma says
that its auxiliary clauses (`CompleteMoments`) follow from the characteristic function identity for a state. -/
theorem gaussianAt_of_characteristic {n : ℕ} (ρ : State (Occupation (Fin n)))
    (d : Fin n × Fin 2 → ℝ) (γ : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hγ : γ.transpose = γ)
    (h : ∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic ρ.coefficients ξ =
      Complex.exp (((-varianceForm γ ξ / 4 : ℝ) : ℂ) + Complex.I * (meanForm d ξ : ℂ))) :
    GaussianAt ρ.coefficients d γ := by sorry

end BosonicLearn
