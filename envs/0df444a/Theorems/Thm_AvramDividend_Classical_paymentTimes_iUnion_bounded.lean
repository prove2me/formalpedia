-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_iUnion_bounded
-- name    : AvramDividend.Classical.paymentTimes_iUnion_bounded
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-08T09:26:05.709979+00:00
-- url     : https://prove2.me/theorems/cffe386d-462d-444d-b629-9eb365b20a64
-- title:
--   All pre-ruin dividend payment times are exhausted by finite natural time horizons
-- statement:
--   For any ruin horizon σ in extended nonnegative reals, the set of dividend payment times [0,σ)∪{0} is exactly the increasing union over natural N of its restriction to times t≤N. This is the precise pathwise exhaustion required to pass from the bounded-time stochastic verification estimates to unrestricted dividendValue by monotone convergence.
-- source:
--   Exact paymentTimes definition and Archimedean exists_nat_ge for real times.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.paymentTimes_iUnion_bounded
    (σ : ℝ≥0∞) :
    (⋃ n : ℕ, paymentTimes σ ∩ Iic (n : ℝ)) = paymentTimes σ := by sorry
