-- Prove2me | Theorems.Thm_AvramDividend_Classical_renewal_quotient_le_of_finite_cycle_bounds
-- name    : AvramDividend.Classical.renewal_quotient_le_of_finite_cycle_bounds
-- status  : Disproved
-- author  : @WillR
-- created : 2026-10-24T09:22:36.085259+00:00
-- url     : https://prove2.me/theorems/b6bfa681-0ba1-450b-8d01-f5bde8ea0337
-- title:
--   Renewal quotient lower bound from finite geometric cycle bounds
-- statement:
--   Analytic close of a geometric renewal lower-bound argument. If, for every cycle count N and every small mesh eps in (0,a), the N-th finite geometric partial sum eps * sum_{k<N} r(eps)^{k+1} with ratio r(eps) = W(a-eps)/W(a) in [0,1) is bounded above by V, then passing N to infinity gives eps*r/(1-r) <= V, and passing eps to zero through the derivative HasDerivAt W d a (with d nonzero) yields ofReal(W(a)/d) <= V. This isolates the purely analytic limit passage of the barrier-supremum renewal argument (Proposition 1 proof path) from its stochastic per-cycle estimates.
-- source:
--   Analytic close of the stopped-renewal geometric-sum argument for Proposition 1 (barrier_strategy_value): the deterministic passage from finite N-cycle discounted bounds to the scale-derivative ratio, assuming the per-cycle stochastic estimates as hypotheses

import Mathlib

open Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

theorem renewal_quotient_le_of_finite_cycle_bounds
    (V : ℝ≥0∞) (W : ℝ → ℝ) (a d : ℝ)
    (hD : HasDerivAt W d a) (hd : d ≠ 0)
    (hWa : 0 < W a)
    (hW8 : ∀ ε : ℝ, 0 < ε → ε < a → 0 ≤ W (a - ε))
    (hlt : ∀ ε : ℝ, 0 < ε → ε < a → W (a - ε) < W a)
    (hfin : ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < a →
      ∑ k ∈ Finset.range N,
        ENNReal.ofReal ε * (ENNReal.ofReal (W (a - ε) / W a)) ^ (k + 1) ≤ V) :
    ENNReal.ofReal (W a / d) ≤ V := by sorry

end AvramDividend.Classical
