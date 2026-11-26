-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqDivisionOperatorInput_apply
-- name    : ClassicalComplexWPT.seqDivisionOperatorInput_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:00:42.206544+00:00
-- url     : https://prove2.me/theorems/5b5540b0-f6f6-53a7-bc28-83e3aaf4e34c
-- title:
--   Classical Complex WPT: seq Division Operator Input apply
-- statement:
--   The Classical Complex WPT construction uses the seq Division Operator Input apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L641-L642
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L641-L642

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqDivisionOperatorInput_apply (d : ℕ) (pf : L1Coeff ℕ × L1Coeff ℕ) :
    seqDivisionOperatorInput d pf = seqDivisionPerturbation d pf.1 := by sorry

attribute [defeq] ClassicalComplexWPT.seqDivisionOperatorInput_apply
