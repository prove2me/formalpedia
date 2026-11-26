-- Prove2me | Theorems.Thm_ClassicalComplexWPT_preparationQuotientEval_zero
-- name    : ClassicalComplexWPT.preparationQuotientEval_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:10:13.406564+00:00
-- url     : https://prove2.me/theorems/c8c969ec-deda-54f2-b729-f0d2c7fd6853
-- title:
--   Classical Complex WPT: preparation Quotient Eval zero
-- statement:
--   The Classical Complex WPT construction uses the preparation Quotient Eval zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L123-L128
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L123-L128

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

theorem ClassicalComplexWPT.preparationQuotientEval_zero {n : ℕ}
    (p : FormalMultilinearSeries ℂ (Ambient n) ℂ) (r : ℝ≥0)
    (hr : (r : ℝ≥0∞) < p.radius) (d : ℕ) :
    preparationQuotientEval p r hr d 0 =
      normalizedPreparationQuotient p r hr d 0 0 := by sorry
