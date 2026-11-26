-- Prove2me | Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_convolution
-- name    : ClassicalComplexWPT.evalL1PowerSeries_convolution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:06:53.207986+00:00
-- url     : https://prove2.me/theorems/67b5c684-8d9f-46c1-8e47-91cf4eaf8cc7
-- title:
--   Classical Complex WPT: eval L1 Power Series convolution
-- statement:
--   Evaluation turns `ℓ¹` convolution into multiplication inside the unit disc.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PowerSeries.lean#L123-L145
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PowerSeries.lean#L123-L145

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.evalL1PowerSeries_convolution (a b : L1Sequence) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries (convolution a b) w =
      evalL1PowerSeries a w * evalL1PowerSeries b w := by sorry
