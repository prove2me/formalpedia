-- Prove2me | Theorems.Thm_AvramDividend_Classical_renewal_quotient_limit_le_of_finite_cycle_bounds
-- name    : AvramDividend.Classical.renewal_quotient_limit_le_of_finite_cycle_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:01:52.420752+00:00
-- url     : https://prove2.me/theorems/398d7971-4510-4579-abc1-a03ee2e0775d
-- title:
--   Limit renewal-quotient bound from finite cycle sums with positive barrier
-- statement:
--   For a positive barrier a, if W is differentiable at a with nonzero derivative d, W a is positive, and W stays nonnegative and strictly below W a on (0, a) from the left, then a uniform ENNReal bound V on all finite geometric cycle sums forces the limit quotient W a / d under the bound. This is the epsilon-to-zero limit of the pointwise renewal-quotient bound and the analytic half of the stopped-renewal lower-bound passage.
-- source:
--   Authored helper restoring the positive-barrier hypothesis dropped in AvramDividend.Classical.renewal_quotient_le_of_finite_cycle_bounds (which is false as stated: V=0, W=(·+2), a=-1, d=1 satisfies every hypothesis vacuously while concluding 1 ≤ 0). Feeds the stopped-renewal lower bound for Proposition 1 of Avram-Palmowski-Pistorius (2007); per-epsilon step is the Proved renewal_quotient_pointwise_bound_of_finite_cycle_sums.

import Mathlib

open Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

theorem renewal_quotient_limit_le_of_finite_cycle_bounds
    (V : ℝ≥0∞) (W : ℝ → ℝ) (a d : ℝ) (ha : 0 < a)
    (hD : HasDerivAt W d a) (hd : d ≠ 0)
    (hWa : 0 < W a)
    (hW8 : ∀ ε : ℝ, 0 < ε → ε < a → 0 ≤ W (a - ε))
    (hlt : ∀ ε : ℝ, 0 < ε → ε < a → W (a - ε) < W a)
    (hfin : ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < a →
      ∑ k ∈ Finset.range N,
        ENNReal.ofReal ε * (ENNReal.ofReal (W (a - ε) / W a)) ^ (k + 1) ≤ V) :
    ENNReal.ofReal (W a / d) ≤ V := by sorry

end AvramDividend.Classical
