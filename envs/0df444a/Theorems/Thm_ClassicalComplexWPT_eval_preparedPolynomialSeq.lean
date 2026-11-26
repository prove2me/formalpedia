-- Prove2me | Theorems.Thm_ClassicalComplexWPT_eval_preparedPolynomialSeq
-- name    : ClassicalComplexWPT.eval_preparedPolynomialSeq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T18:12:13.386258+00:00
-- url     : https://prove2.me/theorems/5ea8060b-f34a-45aa-aa3e-d45209aa6b90
-- title:
--   Classical Complex WPT: eval prepared Polynomial Seq
-- statement:
--   Evaluation of the normalized prepared-polynomial coefficient sequence.
--
--   Source: https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L200-L216
-- source:
--   https://github.com/BochaoKong/classical-complex-wpt/blob/b4a7273fe5c9752753c52e10494097569089642d/ClassicalComplexWPT/PreparationUniqueness.lean#L200-L216

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

theorem ClassicalComplexWPT.eval_preparedPolynomialSeq {n d : ℕ} (r : ℝ≥0) (hr : 0 < r)
    (a : Fin d → Base n → ℂ) (z : Base n) {w : ℂ} (hw : ‖w‖ < 1) :
    evalL1PowerSeries (seqLowShift d constantOneSeq + preparedTailSeq r d a z) w =
      (((r : ℂ) ^ d)⁻¹) * preparedPolynomial d a (z, (r : ℂ) * w) := by sorry
