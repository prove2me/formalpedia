-- Prove2me | Theorems.Thm_BosonicLearn_state_ext_characteristic
-- name    : BosonicLearn.state_ext_characteristic
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T20:57:19.4912+00:00
-- url     : https://prove2.me/theorems/ef963dea-9634-4538-a18b-aea8788135ca
-- title:
--   A state on the Fock space is determined by its Weyl characteristic function
-- statement:
--   Injectivity of the characteristic function on states.
--
--   Let $\rho,\sigma$ be states (density operators) on the $n$-mode Fock space. If
--
--   $$
--   \operatorname{Tr}\big(\rho\,e^{i\xi\cdot\hat r}\big)=\operatorname{Tr}\big(\sigma\,e^{i\xi\cdot\hat r}\big)\qquad\text{for all }\xi\in\mathbb R^{2n},
--   $$
--
--   then $\rho=\sigma$.
--
--   Role. This is what makes the notation $\rho(\mu,\Sigma)$ of the paper legitimate ("such a state is completely determined by its first and second moments"): a Gaussian state is determined by its characteristic function $\exp(i\xi\cdot\mu-\tfrac12\xi^T\Sigma\xi)$. It is used to identify displaced Gaussian states (`BosonicLearn.traceDist_gaussian_common_mean`).
--
--   **Formalization Note** The characteristic function is the published `Support50.P14.oscillatorCharacteristic`; the conclusion is equality of the Fock coefficient arrays.
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

/-- **A state is determined by its Weyl characteristic function.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, pp. 4–5: "Such a state is completely determined by its first and second moments … thus we denote a Gaussian state by
ρ(µ, Σ)" (a Gaussian state is determined by its characteristic function `exp(iξ·µ − ½ ξᵀΣξ)`).

If two states `ρ, σ` on the `n`-mode Fock space have the same characteristic function,
`Tr(ρ e^{iξ·r̂}) = Tr(σ e^{iξ·r̂})` for all `ξ ∈ ℝ²ⁿ`, then `ρ = σ`.

**Formalization Note.** The characteristic function is the published `Support50.P14.oscillatorCharacteristic`; the
conclusion is equality of the Fock coefficient arrays. -/
theorem state_ext_characteristic {n : ℕ} (ρ σ : State (Occupation (Fin n)))
    (h : ∀ ξ : Fin n × Fin 2 → ℝ,
      oscillatorCharacteristic ρ.coefficients ξ = oscillatorCharacteristic σ.coefficients ξ) :
    ρ.coefficients = σ.coefficients := by sorry

end BosonicLearn
