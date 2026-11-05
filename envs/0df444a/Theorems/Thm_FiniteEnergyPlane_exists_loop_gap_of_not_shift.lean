-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_loop_gap_of_not_shift
-- name    : FiniteEnergyPlane.exists_loop_gap_of_not_shift
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T16:15:34.942696+00:00
-- url     : https://prove2.me/theorems/ac01b22c-b433-4300-a98b-617d93e23cec
-- title:
--   Uniform $C^0$ gap between normalized loops of different Reeb orbits
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level and $P=(x,T)$, $Q=(y,T')$ periodic Reeb orbits on $S$. Suppose it is not the case that $T=T'$ and $x(\tau)=y(\tau+c)$ for some $c$ and all $\tau$. Then there is $\delta>0$ such that for all phases $c,c'$ we have $\sup_t\|x(Tt+c)-y(T't+c')\|\ge\delta$.
--
--   **Formalization Note** The conclusion is stated as: for all $c,c'$ there is $t$ with $\delta\le\|x(Tt+c)-y(T't+c')\|$ (sup norm on $\mathbb{R}^{2n+2}$). An orbit and its multiple cover count as different orbits here, since their periods differ.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, § 4.4

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Two periodic Reeb orbits `P`, `Q` that are not time shifts of each other with the same period
have normalized loops `t ↦ P.x (P.T t + c)` and `t ↦ Q.x (Q.T t + c')` at `C⁰`-distance at least
`δ > 0` for all phases `c, c'`. -/
theorem exists_loop_gap_of_not_shift {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P Q : ReebOrbit H)
    (hPQ : ¬ (P.T = Q.T ∧ ∃ c : ℝ, ∀ τ : ℝ, P.x τ = Q.x (τ + c))) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ c c' : ℝ, ∃ t : ℝ,
      δ ≤ ‖P.x (P.T * t + c) - Q.x (Q.T * t + c')‖ := by
  sorry

end FiniteEnergyPlane
