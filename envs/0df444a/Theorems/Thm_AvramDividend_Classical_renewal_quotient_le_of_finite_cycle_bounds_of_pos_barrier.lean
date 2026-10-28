-- Prove2me | Theorems.Thm_AvramDividend_Classical_renewal_quotient_le_of_finite_cycle_bounds_of_pos_barrier
-- name    : AvramDividend.Classical.renewal_quotient_le_of_finite_cycle_bounds_of_pos_barrier
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:24:24.595985+00:00
-- url     : https://prove2.me/theorems/3dfb6dc6-c8b0-4101-b1b4-1607113282e6
-- title:
--   Renewal quotient lower bound from finite geometric cycle bounds at a positive barrier
-- statement:
--   Analytic close of a geometric renewal lower-bound argument at a positive barrier a > 0. If, for every cycle count N and every mesh eps in (0,a), the N-th finite geometric partial sum eps * sum_{k<N} r(eps)^{k+1} with ratio r(eps) = W(a-eps)/W(a) in [0,1) is bounded above by V, then passing N to infinity gives eps*r/(1-r) <= V, and passing eps to zero through the derivative HasDerivAt W d a (with d nonzero) yields ofReal(W(a)/d) <= V. This supersedes renewal_quotient_le_of_finite_cycle_bounds, whose statement omitted the positivity hypothesis 0 < a and is false without it (all eps-premises hold vacuously at a = 0 while the conclusion can fail).
-- source:
--   Corrected variant of renewal_quotient_le_of_finite_cycle_bounds (which omits 0 < a and is false as stated: at a = 0 all eps-premises are vacuous while e.g. W = (·+5), d = 1, V = 0 refutes the conclusion). Analytic close of the stopped-renewal geometric-sum argument for Proposition 1 (barrier_strategy_value).

import Mathlib

open Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

theorem renewal_quotient_le_of_finite_cycle_bounds_of_pos_barrier
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
