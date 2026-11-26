-- Prove2me | Theorems.Thm_ClassicalComplexWPT_exists_weightedLastCoeffs_on_baseBall
-- name    : ClassicalComplexWPT.exists_weightedLastCoeffs_on_baseBall
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:04:24.29442+00:00
-- url     : https://prove2.me/theorems/64764ed8-d5ee-57e5-a75f-b31f3e25d4db
-- title:
--   Classical Complex WPT: exists weighted Last Coeffs on base Ball
-- statement:
--   Explicit `ℓ¹` membership and norm control, uniformly on any smaller base
--   ball whose radius plus the distinguished weight stays inside `p.radius`.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L454-L471
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/WeightedCoefficientMap.lean#L454-L471

import Definitions.Def_ClassicalComplexWPT_AnalyticSeries
import Mathlib.Analysis.Normed.Lp.lpSpace
import Definitions.Def_ClassicalComplexWPT_WeightedCoefficientMap
set_option autoImplicit true
open scoped NNReal ENNReal Topology
open ClassicalComplexWPT
set_option maxHeartbeats 800000

theorem ClassicalComplexWPT.exists_weightedLastCoeffs_on_baseBall {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (s r : ℝ≥0)
    (hsr : (s + r : ℝ≥0∞) < p.radius) {z : Base n}
    (hz : z ∈ Metric.eball (0 : Base n) s) :
    ∃ c : WeightedSeq,
      (∀ k, c k = (r : ℂ) ^ k * lastTaylorCoefficient p k z) ∧
        ‖c‖ ≤ ∑' k : ℕ, ‖p.changeOrigin (z, 0) k‖ * (r : ℝ) ^ k := by sorry
