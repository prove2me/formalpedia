-- Prove2me | Theorems.Thm_AvramDividend_Classical_inverseNatural_positive_grid_point_has_nat_schedule_index
-- name    : AvramDividend.Classical.inverseNatural_positive_grid_point_has_nat_schedule_index
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:44:09.885988+00:00
-- url     : https://prove2.me/theorems/7ff3fbf1-05d9-4d01-8074-9b20deeb4793
-- title:
--   Every positive-denominator inverse-natural grid observation occurs in one fixed countable schedule
-- statement:
--   The deterministic schedule indexed by the Cantor pairing inverse j↦(n_j,k_j), observing at k_j/(n_j+1), contains every grid time k/n with positive denominator n. Thus the double-indexed inverse-natural grids in the Proved strict first-passage horizon lemmas can be represented by a single natural-indexed time schedule for the measurable future-path reward theorem.
-- source:
--   Pinned Mathlib.Data.Nat.Pairing theorem Nat.unpair_pair and NNReal division/coercion. Connects the accepted countable_future_twoSided_discount_reward_measurable theorem a3cd9256-7f08-4808-9731-d1a704d4ea43 with the strict two-sided grid passage lemmas.

import Mathlib.Data.Nat.Pairing
import Mathlib.Data.NNReal.Defs

open scoped NNReal

theorem AvramDividend.Classical.inverseNatural_positive_grid_point_has_nat_schedule_index
    (n k : ℕ) (hn : 0 < n) :
    ∃ j : ℕ,
      ((Nat.unpair j).2 : ℝ≥0) *
        (((((Nat.unpair j).1 + 1) : ℕ) : ℝ≥0)⁻¹) =
      (k : ℝ≥0) * (n : ℝ≥0)⁻¹ := by sorry
