-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_ne_of_isNondegenerateEnd
-- name    : FiniteEnergyPlane.exists_ne_of_isNondegenerateEnd
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T11:58:38.587207+00:00
-- url     : https://prove2.me/theorems/0acdf9fa-58cb-4138-b540-19ed51bac46b
-- title:
--   A map with a nondegenerate end is nonconstant
-- statement:
--   Let $u:\mathbb{C}\to\mathbb{R}^{2n+2}$, let $e:\mathbb{R}\times\mathbb{R}\to\mathbb{C}$ be an end parametrisation, $P=(x,T)$ a periodic Reeb orbit and $\varepsilon\neq0$. If $u$ has a nondegenerate end along $e$ asymptotic to $P$ with sign $\varepsilon$ (Hryniewicz, Definition 2.9 (1), (2), (4)), then $u$ is not constant.
--
--   Typical use: a finite-energy plane or punctured curve with a nondegenerate puncture is nonconstant, so results stated for nonconstant curves (such as positivity of the $d\lambda$-energy) apply to it.
--
--   **Formalization Note** The hypothesis is `IsNondegenerateEnd H u e P ε` with `ε ≠ 0`; the conclusion is `∃ z₁ z₂, u z₁ ≠ u z₂`. No holomorphicity or energy assumption is needed.
-- source:
--   U. Hryniewicz, Trans. AMS 364 (2012), Definition 2.9 and Remark 3.20

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

/-- A map with a nondegenerate end (Hryniewicz, Definition 2.9) of nonzero sign `ε` is
nonconstant. -/
theorem exists_ne_of_isNondegenerateEnd {n : ℕ} (H : V n → ℝ) (u : ℂ → V n)
    (e : ℝ → ℝ → ℂ) (P : ReebOrbit H) {ε : ℝ} (hε : ε ≠ 0)
    (hnd : IsNondegenerateEnd H u e P ε) : ∃ z₁ z₂, u z₁ ≠ u z₂ := by
  sorry

end FiniteEnergyPlane
