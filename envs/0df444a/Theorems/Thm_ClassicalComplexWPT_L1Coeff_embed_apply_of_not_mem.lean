-- Prove2me | Theorems.Thm_ClassicalComplexWPT_L1Coeff_embed_apply_of_not_mem
-- name    : ClassicalComplexWPT.L1Coeff.embed_apply_of_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:01:14.131988+00:00
-- url     : https://prove2.me/theorems/f621e373-3e69-45bb-a277-407521174e70
-- title:
--   L1 Coeff: embed apply of not mem
-- statement:
--   The L1 Coeff construction uses the embed apply of not mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L66-L67
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/L1Division.lean#L66-L67

import Definitions.Def_ClassicalComplexWPT_WeightedSeries
import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Analytic.Constructions
import Definitions.Def_ClassicalComplexWPT_L1Division
set_option autoImplicit true
open Finset
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT
open ClassicalComplexWPT.L1Coeff
variable {I J : Type*}

theorem ClassicalComplexWPT.L1Coeff.embed_apply_of_not_mem (e : I ↪ J) (f : L1Coeff I) (j : J)
    (hj : j ∉ Set.range e) : embed e f j = 0 := by sorry
