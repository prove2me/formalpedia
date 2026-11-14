-- Prove2me | Theorems.Thm_BosonicLearn_state_displace_pair
-- name    : BosonicLearn.state_displace_pair
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T20:30:41.936199+00:00
-- url     : https://prove2.me/theorems/61b9d30c-8607-44a4-b5a3-5ae31edfd3a9
-- title:
--   Displacing two states by the same vector: $\chi\mapsto e^{i\xi\cdot\delta}\chi$ and the trace distance is unchanged
-- statement:
--   Displaced states and invariance of the trace norm under a common displacement.
--
--   Let $\rho,\sigma$ be states on the $n$-mode Fock space and $\delta\in\mathbb R^{2n}$. Then there are states $\rho',\sigma'$ — the displaced states $D_\delta\rho D_\delta^\dagger$ and $D_\delta\sigma D_\delta^\dagger$ — such that
--
--   $$
--   \chi_{\rho'}(\xi)=e^{i\xi\cdot\delta}\chi_\rho(\xi),\qquad\chi_{\sigma'}(\xi)=e^{i\xi\cdot\delta}\chi_\sigma(\xi)\quad(\xi\in\mathbb R^{2n}),\qquad\|\rho'-\sigma'\|_1=\|\rho-\sigma\|_1 ,
--   $$
--
--   where $\chi_\rho(\xi)=\operatorname{Tr}(\rho\,e^{i\xi\cdot\hat r})$.
--
--   Role. In the proof of Theorem 8 the estimated mean is corrected by a displacement, which "does not change their trace distance"; with `BosonicLearn.state_ext_characteristic` this gives `BosonicLearn.traceDist_gaussian_common_mean`.
--
--   **Formalization Note** $\delta$ and $\xi$ are in the interleaved quadrature coordinates of `Support50.P14.oscillatorCharacteristic`, $\xi\cdot\delta$ is `meanForm δ ξ`, and the trace norm is `traceSize`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, proof of Theorem 8, p. 62 ("a common displacement is implemented by the same unitary on both states, so it does not change their trace distance"; the estimator's covariance dominates the true one)

import Mathlib
import Definitions.Def_BosonicLearn_husimiQ
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open MeasureTheory
open scoped ENNReal

namespace BosonicLearn

/-- **Displacing two states by the same phase-space vector.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, proof of Theorem 8, p. 62: "a common displacement is implemented by the same unitary on both states, so it does not change
their trace distance"; §1.1, pp. 4–5 (displacement operators).

For states `ρ, σ` on the `n`-mode Fock space and `δ ∈ ℝ²ⁿ` there are states `ρ', σ'` (the displaced states
`D_δ ρ D_δ†`, `D_δ σ D_δ†`) with characteristic functions `χ_{ρ'}(ξ) = e^{iξ·δ} χ_ρ(ξ)`, `χ_{σ'}(ξ) = e^{iξ·δ} χ_σ(ξ)`,
and `‖ρ' − σ'‖₁ = ‖ρ − σ‖₁`.

**Formalization Note.** `δ` and `ξ` are in the interleaved quadrature coordinates of
`Support50.P14.oscillatorCharacteristic`, and `ξ·δ` is `meanForm δ ξ`. The trace norm is `traceSize`. -/
theorem state_displace_pair {n : ℕ} (ρ σ : State (Occupation (Fin n))) (δ : Fin n × Fin 2 → ℝ) :
    ∃ ρ' σ' : State (Occupation (Fin n)),
      (∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic ρ'.coefficients ξ =
        Complex.exp (Complex.I * (meanForm δ ξ : ℂ)) * oscillatorCharacteristic ρ.coefficients ξ) ∧
      (∀ ξ : Fin n × Fin 2 → ℝ, oscillatorCharacteristic σ'.coefficients ξ =
        Complex.exp (Complex.I * (meanForm δ ξ : ℂ)) * oscillatorCharacteristic σ.coefficients ξ) ∧
      traceSize (ρ'.coefficients - σ'.coefficients) = traceSize (ρ.coefficients - σ.coefficients) := by sorry

end BosonicLearn
