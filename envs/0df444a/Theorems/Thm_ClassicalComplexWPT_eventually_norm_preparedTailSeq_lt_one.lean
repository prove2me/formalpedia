-- Prove2me | Theorems.Thm_ClassicalComplexWPT_eventually_norm_preparedTailSeq_lt_one
-- name    : ClassicalComplexWPT.eventually_norm_preparedTailSeq_lt_one
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:40.061873+00:00
-- url     : https://prove2.me/theorems/9d1dc1c5-7246-5023-b26d-5585b5fab231
-- title:
--   Classical Complex WPT: eventually norm prepared Tail Seq lt one
-- statement:
--   Since all prepared coefficients vanish at the base origin, every fixed
--   positive weighted tail is small on a sufficiently small base neighborhood.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L153-L167
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L153-L167

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_Basic
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.eventually_norm_preparedTailSeq_lt_one {n d : ℕ} (r : ℝ≥0)
    (a : Fin d → Base n → ℂ)
    (ha : ∀ i, AnalyticAt ℂ (a i) 0) (ha0 : ∀ i, a i 0 = 0) :
    ∀ᶠ z in nhds (0 : Base n), ‖preparedTailSeq r d a z‖ < 1 := by sorry
