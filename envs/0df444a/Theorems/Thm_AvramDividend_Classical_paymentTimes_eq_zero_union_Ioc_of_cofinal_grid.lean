-- Prove2me | Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_zero_union_Ioc_of_cofinal_grid
-- name    : AvramDividend.Classical.paymentTimes_eq_zero_union_Ioc_of_cofinal_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T16:51:06.491663+00:00
-- url     : https://prove2.me/theorems/153f3dd1-dfa8-4cc8-bd59-1108ed4e24f6
-- title:
--   Strict payment-time window equals initial time plus open-left Stieltjes prefixes of any cofinal surviving grid
-- statement:
--   Precisely separate the initial time-zero payment endpoint from positive-time Stieltjes payment windows. For any deterministic countable grid lying strictly below a given stopping horizon and cofinal in the strictly surviving positive times, the paymentTimes set is the singleton zero together with the union of intervals (0, grid n]. This endpoint-compatible representation combines with the accepted zero-initial-dividend-atom theorem and finite-activity Stieltjes prefix equalities to identify the complete stopped dividend reward.
-- source:
--   Definition of paymentTimes and zero-barrier Stieltjes reward, Avram Palmowski Pistorius (2007) §3.3.

import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Mathlib.Data.ENNReal.Real
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.paymentTimes_eq_zero_union_Ioc_of_cofinal_grid
    (σ : ℝ≥0∞) (grid : ℕ → ℝ≥0)
    (hbelow : ∀ n : ℕ, (grid n : ℝ≥0∞) < σ)
    (hcofinal : ∀ t : ℝ, 0 < t → ENNReal.ofReal t < σ →
      ∃ n : ℕ, t ≤ (grid n : ℝ)) :
    paymentTimes σ =
      {(0 : ℝ)} ∪ ⋃ n : ℕ, Ioc (0 : ℝ) (grid n : ℝ) := by sorry
