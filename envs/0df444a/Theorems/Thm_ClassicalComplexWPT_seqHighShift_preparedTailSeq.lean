-- Prove2me | Theorems.Thm_ClassicalComplexWPT_seqHighShift_preparedTailSeq
-- name    : ClassicalComplexWPT.seqHighShift_preparedTailSeq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:11:27.052447+00:00
-- url     : https://prove2.me/theorems/c1373767-a09b-404b-9152-bd2b04d3beb7
-- title:
--   Classical Complex WPT: seq High Shift prepared Tail Seq
-- statement:
--   Prepared tails have no coefficients in degrees at least `d`.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L97-L114
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L97-L114

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

theorem ClassicalComplexWPT.seqHighShift_preparedTailSeq {n d : ℕ} (r : ℝ≥0)
    (a : Fin d → Base n → ℂ) (z : Base n) :
    seqHighShift d (preparedTailSeq r d a z) = 0 := by sorry
