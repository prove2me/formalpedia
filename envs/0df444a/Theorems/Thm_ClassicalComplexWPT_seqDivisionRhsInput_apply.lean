-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqDivisionRhsInput_apply
-- name    : ClassicalComplexWPT.seqDivisionRhsInput_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:50.097059+00:00
-- url     : https://prove2.me/theorems/6528d46c-01f7-5704-80dd-70c42d6e5bfb
-- title:
--   Classical Complex WPT: seq Division Rhs Input apply
-- statement:
--   The Classical Complex WPT construction uses the seq Division Rhs Input apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L644-L645
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L644-L645

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqDivisionRhsInput_apply (d : ℕ) (pf : L1Coeff ℕ × L1Coeff ℕ) :
    seqDivisionRhsInput d pf = seqHighShift d pf.2 := by sorry

attribute [defeq] ClassicalComplexWPT.seqDivisionRhsInput_apply
