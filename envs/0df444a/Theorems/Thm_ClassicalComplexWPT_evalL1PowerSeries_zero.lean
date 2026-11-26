-- Prove2me | Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_zero
-- name    : ClassicalComplexWPT.evalL1PowerSeries_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:10:11.242402+00:00
-- url     : https://prove2.me/theorems/26fc3706-0870-5b59-b149-6a21eaeba3c5
-- title:
--   Classical Complex WPT: eval L1 Power Series zero
-- statement:
--   The Classical Complex WPT construction uses the eval L1 Power Series zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L22-L28
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PublicExistence.lean#L22-L28

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

theorem ClassicalComplexWPT.evalL1PowerSeries_zero (a : L1Sequence) :
    evalL1PowerSeries a 0 = a 0 := by sorry
