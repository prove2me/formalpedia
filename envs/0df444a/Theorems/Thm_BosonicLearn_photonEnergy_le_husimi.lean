-- Prove2me | Theorems.Thm_BosonicLearn_photonEnergy_le_husimi
-- name    : BosonicLearn.photonEnergy_le_husimi
-- status  : Proved
-- author  : @Senrui Chen
-- created : 2026-11-13T20:34:47.676587+00:00
-- url     : https://prove2.me/theorems/367ce1da-28e9-4ba6-b751-4299b46419fe
-- title:
--   Mean photon number is dominated by the second moment of the Husimi function: $\sum_u|u|\rho_{uu}\le\int\frac{|\beta|^2}2Q_\rho(\beta)\,d\beta$
-- statement:
--   A bound on the mean photon number of a state by its heterodyne statistics.
--
--   For every state $\rho$ on the $n$-mode Fock space, with Husimi function $Q_\rho(\beta)=(2\pi)^{-n}\langle\alpha(\beta)|\rho|\alpha(\beta)\rangle$ in heterodyne coordinates $\beta\in\mathbb R^{2n}$,
--
--   $$
--   \sum_{u\in\mathbb N^n}|u|\,\langle u|\rho|u\rangle\ \le\ \int_{\mathbb R^{2n}}\frac{|\beta|^2}{2}\,Q_\rho(\beta)\,d\beta .
--   $$
--
--   (In fact the right-hand side equals $\operatorname{Tr}(\rho\sum_j\hat a_j\hat a_j^\dagger)=\sum_u(|u|+n)\rho_{uu}$; only the inequality is stated.)
--
--   Role. It gives the finite-energy clause of the definition of a Gaussian state from the heterodyne law (`BosonicLearn.gaussianAt_of_characteristic`).
--
--   **Formalization Note** Both sides are in $[0,\infty]$: the left side is the published `Support50.P14.photonEnergy`, the right side a lower Lebesgue integral of `ENNReal.ofReal ((∑ a, β a ^ 2) / 2 * husimiQ ρ.coefficients β)`.
-- source:
--   Chen, Anna Mele, Anna Mele, Preskill, When are bosonic Gaussian states classical to learn?, arXiv:2609.26705, §1.1, Eqs. (2) and (4), pp. 4–5 (Gaussian states, displacement operators, characteristic function); §1.1, p. 5 (heterodyne measurement)

import Mathlib
import Definitions.Def_BosonicLearn_husimiQ
import Definitions.Def_QAlgorithms_Papers_Independent_Support50_P14

open QAlgorithms.Papers.Independent.Dependency50.P33 (State traceSize)
open QAlgorithms.Papers.Independent.Claimed50.P47 (Occupation)
open QAlgorithms.Papers.Independent.Support50.P14
open MeasureTheory
open scoped ENNReal

namespace BosonicLearn

/-- **Mean photon number is dominated by the second moment of the Husimi function.**
Chen, Anna Mele, Anna Mele, Preskill, *When are bosonic Gaussian states classical to learn?*, arXiv:2609.26705, §1.1, p. 5 (heterodyne measurement and the Husimi function); the finite-energy requirement in the definition of a Gaussian
state.

For every state `ρ` on the `n`-mode Fock space,
`∑ᵤ |u| ⟨u|ρ|u⟩ ≤ ∫ (|β|²/2) Q_ρ(β) dβ`, where `Q_ρ` is the Husimi function in heterodyne coordinates.

**Formalization Note.** In fact `∫ (|β|²/2) Q_ρ dβ = Tr(ρ ∑ⱼ âⱼâⱼ†) = ∑ᵤ (|u| + n) ρ_uu` (anti-normal ordering); only the
inequality is stated. Both sides are in `ℝ≥0∞`: the left side is `Support50.P14.photonEnergy`. -/
theorem photonEnergy_le_husimi {n : ℕ} (ρ : State (Occupation (Fin n))) :
    photonEnergy ρ.coefficients ≤
      ∫⁻ β : Fin n ⊕ Fin n → ℝ, ENNReal.ofReal ((∑ a, β a ^ 2) / 2 * husimiQ ρ.coefficients β) := by sorry

end BosonicLearn
