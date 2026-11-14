-- Prove2me | Theorems.Thm_BosonicLearn_state_gaussian_mixture
-- name    : BosonicLearn.state_gaussian_mixture
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T20:59:55.587861+00:00
-- url     : https://prove2.me/theorems/1883b54f-ec72-4297-aa75-d7b98b604123
-- title:
--   Gaussian mixing of displaced states: a state $\rho'$ with $\chi_{\rho'}(\xi)=\exp(i\xi\cdot m-\tfrac12\xi^TT\xi)\chi_\rho(\xi)$ for $T\succeq0$
-- statement:
--   Additive classical Gaussian noise on a state.
--
--   Let $\rho$ be a state on the $n$-mode Fock space, $m\in\mathbb R^{2n}$ and $T$ a positive semidefinite real $2n\times2n$ matrix. Then there is a state $\rho'$ — the mixture $\int D_x\rho D_x^\dagger\,d\mathcal N(m,T)(x)$ of displaced copies of $\rho$ — with
--
--   $$
--   \chi_{\rho'}(\xi)=\exp\!\big(i\,\xi\cdot m-\tfrac12\,\xi^TT\,\xi\big)\,\chi_\rho(\xi)\qquad(\xi\in\mathbb R^{2n}).
--   $$
--
--   Role. Applied to a Gaussian state $\rho(\mu,\Sigma)$ with $m=\mu'-\mu$, $T=\Sigma'-\Sigma\succeq0$, it produces the Gaussian state $\rho(\mu',\Sigma')$ (`BosonicLearn.gaussianState_exists_of_le`).
--
--   **Formalization Note** $m,\xi,T$ are in the interleaved quadrature coordinates of `Support50.P14.oscillatorCharacteristic`; $\xi\cdot m$ is `meanForm m ξ` and $\xi^TT\xi$ is `varianceForm T ξ`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, proof of Theorem 8, p. 62 ("a common displacement is implemented by the same unitary on both states, so it does not change their trace distance"; the estimator's covariance dominates the true one)

import Mathlib
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open scoped ENNReal Matrix

namespace BosonicLearn

/-- **Classical Gaussian mixing of displaced states (additive Gaussian noise).**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, proof of Theorem 8, p. 62 (the estimator is a Gaussian state whose covariance dominates the true one); §1.1, pp. 4–5.

For a state `ρ` on the `n`-mode Fock space, a vector `m ∈ ℝ²ⁿ` and a positive semidefinite real `2n × 2n` matrix
`T`, there is a state `ρ'` (the mixture `∫ D_x ρ D_x† dN(m, T)(x)` of displaced copies of `ρ`) with characteristic
function `χ_{ρ'}(ξ) = exp(i ξ·m − ½ ξᵀTξ) χ_ρ(ξ)`.

**Formalization Note.** `m, ξ, T` are in the interleaved quadrature coordinates of
`Support50.P14.oscillatorCharacteristic`; `ξ·m` is `meanForm m ξ` and `ξᵀTξ` is `varianceForm T ξ`. -/
theorem state_gaussian_mixture {n : ℕ} (ρ : State (Occupation (Fin n))) (m : Fin n × Fin 2 → ℝ)
    (T : Matrix (Fin n × Fin 2) (Fin n × Fin 2) ℝ) (hT : T.PosSemidef) :
    ∃ ρ' : State (Occupation (Fin n)), ∀ ξ : Fin n × Fin 2 → ℝ,
      oscillatorCharacteristic ρ'.coefficients ξ =
        Complex.exp (Complex.I * (meanForm m ξ : ℂ) - ((varianceForm T ξ / 2 : ℝ) : ℂ)) *
          oscillatorCharacteristic ρ.coefficients ξ := by sorry

end BosonicLearn
