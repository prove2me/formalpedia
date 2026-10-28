-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_renewal_shifted_tsum_eq_unshifted
-- name    : AvramDividend.Classical.causal_renewal_shifted_tsum_eq_unshifted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:56:09.362468+00:00
-- url     : https://prove2.me/theorems/7c5711a8-9b63-4de8-ba6a-f82845781a73
-- title:
--   Shifted renewal-density series equals the unshifted infinite series
-- statement:
--   For any summable sequence of real convolution-power evaluations, the renewal-series convention with zero at index zero and previous power at every positive index has exactly the same total as the unshifted series. The result supplies an exact index-normalisation step for renewal-density integrability and Laplace identities.

import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
set_option maxHeartbeats 1000000

theorem AvramDividend.Classical.causal_renewal_shifted_tsum_eq_unshifted
    (F : ℕ → ℝ) (hF : Summable F) :
    (∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1)) =
      ∑' n : ℕ, F n := by sorry
