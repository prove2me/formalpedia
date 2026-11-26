-- Prove2me | Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_smul
-- name    : ClassicalComplexWPT.evalL1PowerSeries_smul
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:38.320852+00:00
-- url     : https://prove2.me/theorems/d1c3c523-324a-563c-a802-42e1b77f9f7a
-- title:
--   Classical Complex WPT: eval L1 Power Series smul
-- statement:
--   The Classical Complex WPT construction uses the eval L1 Power Series smul property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PolynomialEvaluation.lean#L18-L22
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PolynomialEvaluation.lean#L18-L22

import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.evalL1PowerSeries_smul (c : ℂ) (a : L1Sequence) (w : ℂ) :
    evalL1PowerSeries (c • a) w = c * evalL1PowerSeries a w := by sorry
