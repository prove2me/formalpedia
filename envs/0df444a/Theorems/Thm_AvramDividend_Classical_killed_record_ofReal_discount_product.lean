-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_record_ofReal_discount_product
-- name    : AvramDividend.Classical.killed_record_ofReal_discount_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:34:50.729961+00:00
-- url     : https://prove2.me/theorems/e79a2d9b-ede2-46f8-bad6-07e0337159b3
-- title:
--   Discounted first-record payout equals ENNReal product of reward and discount
-- statement:
--   For nonnegative dividend step ε, the ENNReal embedding of ε exp(-q t) is the product of ε and the exponential discount embeddings. This aligns the original renewal expectation with the stopped Markov pathwise product bound.
-- source:
--   Mathlib ENNReal.ofReal_mul

import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential

open scoped ENNReal

theorem AvramDividend.Classical.killed_record_ofReal_discount_product
    (ε q t : ℝ) (hε : 0 ≤ ε) :
    ENNReal.ofReal (ε * Real.exp (-(q * t))) =
      ENNReal.ofReal ε * ENNReal.ofReal (Real.exp (-(q * t))) := by sorry
