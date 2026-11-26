-- Prove2me | Theorems.Thm_ClassicalComplexWPT_preparedTailSeq_eq_iff
-- name    : ClassicalComplexWPT.preparedTailSeq_eq_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:43.296018+00:00
-- url     : https://prove2.me/theorems/34eb61e7-cf75-5989-8163-4d5f0320943e
-- title:
--   Classical Complex WPT: prepared Tail Seq eq iff
-- statement:
--   Equality of normalized prepared tails recovers equality of every
--   coefficient when the weight is positive.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L171-L187
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L171-L187

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

theorem ClassicalComplexWPT.preparedTailSeq_eq_iff {n d : ℕ} {r : ℝ≥0} (hr : 0 < r)
    (a a' : Fin d → Base n → ℂ) (z : Base n) :
    preparedTailSeq r d a z = preparedTailSeq r d a' z ↔
      ∀ i, a i z = a' i z := by sorry
