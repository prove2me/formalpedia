-- Prove2me | Theorems.Thm_ClassicalComplexWPT_preparedTailSeq_apply_fin
-- name    : ClassicalComplexWPT.preparedTailSeq_apply_fin
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:23.758876+00:00
-- url     : https://prove2.me/theorems/9a6bd541-0abe-4ece-a362-0de36988eeb4
-- title:
--   Classical Complex WPT: prepared Tail Seq apply fin
-- statement:
--   The Classical Complex WPT construction uses the prepared Tail Seq apply fin property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L73-L94
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L73-L94

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

theorem ClassicalComplexWPT.preparedTailSeq_apply_fin {n d : ℕ} (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (z : Base n) (i : Fin d) :
    preparedTailSeq r d a z (i : ℕ) =
      (((r : ℂ) ^ d)⁻¹ * (r : ℂ) ^ (i : ℕ)) * a i z := by sorry
