-- Prove2me | Theorems.Thm_ClassicalComplexWPT_preparationUnit_zero_ne
-- name    : ClassicalComplexWPT.preparationUnit_zero_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:13:05.778019+00:00
-- url     : https://prove2.me/theorems/2867ff33-62ca-4a7e-b582-3b80f034c6bd
-- title:
--   Classical Complex WPT: preparation Unit zero ne
-- statement:
--   The Classical Complex WPT construction uses the preparation Unit zero ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L142-L149
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L142-L149

import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedEvaluation
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Definitions.Def_ClassicalComplexWPT_PublicExistence
set_option autoImplicit true
open Filter
open scoped BigOperators ENNReal NNReal Topology
noncomputable section
set_option maxHeartbeats 1000000
open ClassicalComplexWPT

theorem ClassicalComplexWPT.preparationUnit_zero_ne {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ)
    (hr0 : 0 < r) (htop : originWeightedCoeffs p r hr d ≠ 0)
    (hq0 : normalizedPreparationQuotient p r hr d 0 0 = 1) :
    preparationUnit p r hr d 0 ≠ 0 := by sorry
