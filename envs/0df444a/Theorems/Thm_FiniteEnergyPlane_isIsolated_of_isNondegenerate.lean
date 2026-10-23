-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isIsolated_of_isNondegenerate
-- name    : FiniteEnergyPlane.isIsolated_of_isNondegenerate
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-21T12:41:04.368655+00:00
-- url     : https://prove2.me/theorems/b7917bea-abea-47d1-9f49-373086ded951
-- title:
--   Nondegenerate periodic Reeb orbits are isolated
-- statement:
--   Let $S=H^{-1}(1)$ be a strictly star-shaped level and $P=(x,T)$ a nondegenerate periodic Reeb orbit on $S$. Then $P$ is isolated: some open set containing $x(\mathbb{R})$ meets no periodic Reeb orbit of period $T$ whose image is not contained in $x(\mathbb{R})$.
--
--   **Formalization Note** Isolation is `ReebOrbit.IsIsolated` from the previous mission (same period $T$, not necessarily minimal).
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, lecture notes, Humboldt-Universität zu Berlin (2026 version); earlier version arXiv:1612.01009, Exercise 3.1.4

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A nondegenerate periodic Reeb orbit is isolated among the periodic orbits of the same
period, in the sense of `ReebOrbit.IsIsolated`. -/
theorem isIsolated_of_isNondegenerate {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H) (P : ReebOrbit H)
    (hP : P.IsNondegenerate) : P.IsIsolated := by
  sorry

end FiniteEnergyPlane
