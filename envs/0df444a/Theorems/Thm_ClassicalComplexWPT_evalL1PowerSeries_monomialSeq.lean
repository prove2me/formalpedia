-- Prove2me | Theorems.Thm_ClassicalComplexWPT_evalL1PowerSeries_monomialSeq
-- name    : ClassicalComplexWPT.evalL1PowerSeries_monomialSeq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:07:41.469894+00:00
-- url     : https://prove2.me/theorems/d8d5a1ef-05df-5e98-aa52-e2965a11bc45
-- title:
--   Classical Complex WPT: eval L1 Power Series monomial Seq
-- statement:
--   The Classical Complex WPT construction uses the eval L1 Power Series monomial Seq property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PolynomialEvaluation.lean#L24-L29
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1PolynomialEvaluation.lean#L24-L29

import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_NormalizedCoefficients
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.evalL1PowerSeries_monomialSeq (d : ℕ) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries (monomialSeq d) w = w ^ d := by sorry
