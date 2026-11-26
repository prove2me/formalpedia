-- Prove2me | Theorems.Thm_ClassicalComplexWPT_analyticAt_preparedTailSeq
-- name    : ClassicalComplexWPT.analyticAt_preparedTailSeq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:15.104202+00:00
-- url     : https://prove2.me/theorems/6346801f-4c63-42db-93aa-94ea69998d67
-- title:
--   Classical Complex WPT: analytic At prepared Tail Seq
-- statement:
--   The prepared tail varies analytically with the base point.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L117-L149
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L117-L149

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

theorem ClassicalComplexWPT.analyticAt_preparedTailSeq {n d : ℕ} (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (ha : ∀ i, AnalyticAt ℂ (a i) 0) :
    AnalyticAt ℂ (preparedTailSeq r d a) 0 := by sorry
