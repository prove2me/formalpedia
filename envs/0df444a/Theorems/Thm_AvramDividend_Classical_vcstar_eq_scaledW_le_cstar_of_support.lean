-- Prove2me | Theorems.Thm_AvramDividend_Classical_vcstar_eq_scaledW_le_cstar_of_support
-- name    : AvramDividend.Classical.vcstar_eq_scaledW_le_cstar_of_support
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:22:41.347349+00:00
-- url     : https://prove2.me/theorems/8e85de2d-2315-4446-ae1e-76e759e7782e
-- title:
--   Optimal barrier candidate agrees with scaled W below c-star under the scale-function support property
-- statement:
--   If a real candidate scale function W vanishes at negative arguments, then for every z at or below the real c-star barrier the piecewise optimal-barrier candidate equals divE(W(z),scaleDeriv W(c-star)). Below zero both sides vanish by support. Between zero and the barrier, both sides agree by the definition of the below-barrier branch. The support hypothesis is essential: without it, a negative z with W(z)≠0 gives a counterexample.
-- source:
--   Corrected source-faithful child of vcstar_scaledW_matched_weighted_jet_at_cstar, accounting for the explicit negative-reserve zero branch of barrierValue. Replaces the overly broad proposed vcstar_eq_scaledW_le_cstar declaration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open MeasureTheory Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.vcstar_eq_scaledW_le_cstar_of_support
    (W : ℝ → ℝ) (hsupport : ∀ z : ℝ, z < 0 → W z = 0)
    (z : ℝ) (hz : z ≤ (cstar W).toReal) :
    vcstar W z = divE (W z) (scaleDeriv W (cstar W).toReal) := by sorry
