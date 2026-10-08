-- Prove2me | Theorems.Thm_AvramDividend_Classical_ennreal_scale_ratio_cancel
-- name    : AvramDividend.Classical.ennreal_scale_ratio_cancel
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:36:12.679992+00:00
-- url     : https://prove2.me/theorems/5aaab3d9-1489-49e1-9126-d2bad84a98ec
-- title:
--   Cancellation of positive middle scale levels in the nonnegative extended-real value factorisation
-- statement:
--   For nonnegative x and strictly positive scale level a and derivative denominator d, the factors x/a and a/d can be represented in ENNReal and multiplied without loss, cancelling a to yield x/d. This is the exact real-to-extended-real algebra needed after the strong-Markov barrier-scale factor and the reflected boundary value are proved. Independent of stochastic inputs and barrier value, with no circular project imports.
-- source:
--   Avram, Palmowski, Pistorius, Proposition 1 scale-factor and boundary-value multiplication; Mathlib ENNReal.ofReal_mul and field arithmetic.

import Mathlib
open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.ennreal_scale_ratio_cancel
    (x a d : ℝ) (hx : 0 ≤ x) (ha : 0 < a) (hd : 0 < d) :
    ENNReal.ofReal (x / a) * ENNReal.ofReal (a / d) =
      ENNReal.ofReal (x / d) := by sorry
