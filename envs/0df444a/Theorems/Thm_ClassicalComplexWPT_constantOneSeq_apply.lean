-- Prove2me | Theorems.Thm_ClassicalComplexWPT_constantOneSeq_apply
-- name    : ClassicalComplexWPT.constantOneSeq_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:13.299977+00:00
-- url     : https://prove2.me/theorems/359f6882-d11d-5460-9e43-2d89d1475c0d
-- title:
--   Classical Complex WPT: constant One Seq apply
-- statement:
--   The Classical Complex WPT construction uses the constant One Seq apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L39-L44
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L39-L44

import Definitions.Def_ClassicalComplexWPT_L1Division
import Definitions.Def_ClassicalComplexWPT_L1PowerSeries
import Definitions.Def_ClassicalComplexWPT_Basic
import Definitions.Def_ClassicalComplexWPT_L1PolynomialEvaluation
import Definitions.Def_ClassicalComplexWPT_PreparationSequences
import Definitions.Def_ClassicalComplexWPT_WeightedGermEvaluation
import Mathlib.Analysis.Analytic.Uniqueness
import Definitions.Def_ClassicalComplexWPT_PreparationUniqueness
set_option autoImplicit true
open Filter
open scoped ENNReal NNReal Topology
noncomputable section
open ClassicalComplexWPT

theorem ClassicalComplexWPT.constantOneSeq_apply (k : ℕ) :
    constantOneSeq k = if k = 0 then 1 else 0 := by sorry
