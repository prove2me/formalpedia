-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqDivisionGlobal_factorization
-- name    : ClassicalComplexWPT.seqDivisionGlobal_factorization
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:06:44.713802+00:00
-- url     : https://prove2.me/theorems/711704e2-eac9-51fd-971f-7d0466a59d90
-- title:
--   Classical Complex WPT: seq Division Global factorization
-- statement:
--   The Classical Complex WPT construction uses the seq Division Global factorization property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L773-L778
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L773-L778

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.seqDivisionGlobal_factorization (d : ℕ) (p f : L1Coeff ℕ) (hp : ‖p‖ < 1) :
    f = seqLowShift d (seqDivisionQuotientGlobal d (p,f)) +
      convolution (seqDivisionQuotientGlobal d (p,f)) p +
        seqDivisionRemainderGlobal d (p,f) := by sorry
