-- Prove2me | Theorems.Thm_AvramDividend_Classical_ennreal_exp_downcrossing_threshold_iff
-- name    : AvramDividend.Classical.ennreal_exp_downcrossing_threshold_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:52:31.935596+00:00
-- url     : https://prove2.me/theorems/55827011-1908-4e05-8993-c950660c3165
-- title:
--   Extended-real exponential threshold exactly identifies downward crossing
-- statement:
--   For ε>0, b,y real, the inequality ENNReal.ofReal(exp(ε b))≤ENNReal.ofReal(exp(−ε y)) is equivalent to y≤−b. This is the precise event identification needed to convert an Esscher-exponential Markov estimate into a lower-crossing probability bound, including boundary equality.
-- source:
--   Use the pinned ENNReal.ofReal_le_ofReal_iff on positive exponential images, the strict real exponential order equivalence and positivity of ε to cancel the positive multiplier. No Lévy-specific hypotheses are required.

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Algebra.Order.Field.Basic
open scoped ENNReal

theorem AvramDividend.Classical.ennreal_exp_downcrossing_threshold_iff
    (ε b y : ℝ) (hε : 0 < ε) :
    (ENNReal.ofReal (Real.exp (ε * b)) ≤
      ENNReal.ofReal (Real.exp (-ε * y))) ↔ y ≤ -b := by sorry
