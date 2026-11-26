-- Prove2me | Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_eq_tsum
-- name    : ClassicalComplexWPT.evalL1PowerSeries_eq_tsum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T17:59:51.818697+00:00
-- url     : https://prove2.me/theorems/6a8159f1-7e9f-5564-a7dd-c0d44e023627
-- title:
--   Classical Complex WPT: eval L1 Power Series eq tsum
-- statement:
--   Inside the unit disc, bundled evaluation is the usual scalar power-series sum.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PowerSeries.lean#L90-L110
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PowerSeries.lean#L90-L110

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
set_option autoImplicit true
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.evalL1PowerSeries_eq_tsum (a : L1Sequence) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries a w = ∑' k : ℕ, a k * w ^ k := by sorry
