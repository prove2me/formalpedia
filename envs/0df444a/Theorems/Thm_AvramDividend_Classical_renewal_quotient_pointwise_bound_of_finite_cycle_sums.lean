-- Prove2me | Theorems.Thm_AvramDividend_Classical_renewal_quotient_pointwise_bound_of_finite_cycle_sums
-- name    : AvramDividend.Classical.renewal_quotient_pointwise_bound_of_finite_cycle_sums
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:28:01.629651+00:00
-- url     : https://prove2.me/theorems/b993385a-62a4-41ac-8e24-d963afc52e48
-- title:
--   Pointwise renewal quotient bound from finite geometric cycle sums
-- statement:
--   For each fixed mesh eps in (0,a) with cycle ratio r(eps) = W(a-eps)/W(a) in [0,1), if every finite geometric partial sum eps * sum_{k<N} r^{k+1} is bounded above by V, then the closed-form limit eps*r/(1-r) also bounds V from below in ENNReal. This isolates the per-mesh N-to-infinity passage of the renewal lower-bound argument (Proposition 1 proof path) from the final eps-to-zero slope limit.
-- source:
--   Per-mesh N-limit stage of the stopped-renewal geometric-sum argument for Proposition 1 (barrier_strategy_value); extracted as an independently useful lemma so the parent analytic close stays within submission caps

import Mathlib

open Filter Topology
open scoped ENNReal

namespace AvramDividend.Classical

theorem renewal_quotient_pointwise_bound_of_finite_cycle_sums
    (V : ℝ≥0∞) (W : ℝ → ℝ) (a : ℝ) (ha : 0 < a)
    (hr : ∀ ε : ℝ, 0 < ε → ε < a → 0 ≤ W (a - ε) / W a ∧ W (a - ε) / W a < 1)
    (hfin : ∀ (N : ℕ) (ε : ℝ), 0 < ε → ε < a →
      ∑ k ∈ Finset.range N,
        ENNReal.ofReal ε * (ENNReal.ofReal (W (a - ε) / W a)) ^ (k + 1) ≤ V) :
    ∀ ε : ℝ, 0 < ε → ε < a →
      ENNReal.ofReal (ε * (W (a - ε) / W a) / (1 - W (a - ε) / W a)) ≤ V := by sorry

end AvramDividend.Classical
