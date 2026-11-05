-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_shift_of_isNondegenerate_of_near
-- name    : FiniteEnergyPlane.exists_shift_of_isNondegenerate_of_near
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-04T16:22:07.48605+00:00
-- url     : https://prove2.me/theorems/87051ad3-17fa-4374-b58f-6198e8850aa3
-- title:
--   Nondegenerate Reeb orbits are rigid among orbits of nearby period
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^{2n+2}$ be a strictly star-shaped level and $P=(x,T)$ a nondegenerate periodic Reeb orbit on $S$. Then there is $r>0$ such that every periodic Reeb orbit $Q=(y,T')$ with $|T'-T|<r$ and $\|y(0)-x(0)\|<r$ satisfies $T'=T$ and $y(\tau)=x(\tau+c)$ for some $c\in\mathbb{R}$ and all $\tau$.
--
--   **Formalization Note** Compared with `isIsolated_of_isNondegenerate`, the competing orbit is not assumed to have the same period $T$, and $T'$ need not be a minimal period.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859-1931, § 4.4

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Local rigidity of a nondegenerate periodic Reeb orbit `P = (x, T)`, allowing the period to
vary: there is `r > 0` such that every periodic Reeb orbit `Q` with `|Q.T - T| < r` and
`‖Q.x 0 - x 0‖ < r` has period exactly `T` and is a time shift of `P`. -/
theorem exists_shift_of_isNondegenerate_of_near {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H) (hP : P.IsNondegenerate) :
    ∃ r : ℝ, 0 < r ∧ ∀ Q : ReebOrbit H, |Q.T - P.T| < r → ‖Q.x 0 - P.x 0‖ < r →
      Q.T = P.T ∧ ∃ c : ℝ, ∀ τ : ℝ, Q.x τ = P.x (τ + c) := by
  sorry

end FiniteEnergyPlane
