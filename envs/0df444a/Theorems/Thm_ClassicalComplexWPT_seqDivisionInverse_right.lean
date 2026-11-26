-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqDivisionInverse_right
-- name    : ClassicalComplexWPT.seqDivisionInverse_right
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:02:32.184165+00:00
-- url     : https://prove2.me/theorems/36b041be-915f-5195-93f2-7d8bddb37f61
-- title:
--   Classical Complex WPT: seq Division Inverse right
-- statement:
--   The Classical Complex WPT construction uses the seq Division Inverse right property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L603-L612
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L603-L612

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqDivisionInverse_right (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (b : L1Coeff ℕ) :
    seqDivisionInverse d p hp b +
      seqHighShift d (convolution (seqDivisionInverse d p hp b) p) = b := by sorry
