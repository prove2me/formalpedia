-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierValue_deriv_one_of_differentiableAt
-- name    : AvramDividend.Classical.barrierValue_deriv_one_of_differentiableAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T22:10:19.208259+00:00
-- url     : https://prove2.me/theorems/de55cb5b-4ad6-4818-be33-c2dca6f4ea46
-- title:
--   Differentiable barrier value has marginal slope one at the barrier
-- statement:
--   For any nonnegative barrier a and function W, the barrier-value formula is affine with slope one strictly above a. If barrierValue W a is differentiable at a, uniqueness of its right-hand derivative forces its derivative at a to be one. Use the already proved above-barrier affine identity and the unique right-sided derivative on the closed half-line [a, infinity). This is the generic smooth-fit assembly lemma needed at the positive optimal barrier.

import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.TangentCone.Real
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_barrierValue_above_affine
open AvramDividend.Classical Set

theorem AvramDividend.Classical.barrierValue_deriv_one_of_differentiableAt
    (W : ℝ → ℝ) (a : ℝ) (ha : 0 ≤ a)
    (hdiff : DifferentiableAt ℝ (barrierValue W a) a) :
    deriv (barrierValue W a) a = 1 := by sorry
