-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqDivisionQuotient_equation
-- name    : ClassicalComplexWPT.seqDivisionQuotient_equation
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:03:14.707011+00:00
-- url     : https://prove2.me/theorems/e458710b-736c-4053-a92a-9701ba9b1bad
-- title:
--   Classical Complex WPT: seq Division Quotient equation
-- statement:
--   The Classical Complex WPT construction uses the seq Division Quotient equation property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L703-L708
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L703-L708

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqDivisionQuotient_equation (d : ℕ) (p : L1Coeff ℕ) (hp : ‖p‖ < 1)
    (f : L1Coeff ℕ) :
    seqDivisionQuotient d p hp f +
      seqHighShift d (convolution (seqDivisionQuotient d p hp f) p) =
        seqHighShift d f := by sorry
