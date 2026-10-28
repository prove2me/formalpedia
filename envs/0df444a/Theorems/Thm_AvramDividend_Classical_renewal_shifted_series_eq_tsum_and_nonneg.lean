-- Prove2me | Theorems.Thm_AvramDividend_Classical_renewal_shifted_series_eq_tsum_and_nonneg
-- name    : AvramDividend.Classical.renewal_shifted_series_eq_tsum_and_nonneg
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T08:16:46.759079+00:00
-- url     : https://prove2.me/theorems/3a74273e-6315-46d6-9098-be48910475c4
-- title:
--   Nonnegative renewal density sum and its shifted zero-index representation
-- statement:
--   For a summable nonnegative sequence F(n), the series with a zero initial term and subsequent terms F(n-1) has the same sum as the original sequence, and that sum is nonnegative. This matches the precise shifted-index sum occurring in the bounded-variation Esscher renewal density formula.

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Topology.Algebra.InfiniteSum.Order

theorem AvramDividend.Classical.renewal_shifted_series_eq_tsum_and_nonneg
    (F : ℕ → ℝ) (hF : Summable F) (hF0 : ∀ n : ℕ, 0 ≤ F n) :
    (∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1)) =
      (∑' n : ℕ, F n) ∧
      0 ≤ (∑' n : ℕ, F n) := by sorry
