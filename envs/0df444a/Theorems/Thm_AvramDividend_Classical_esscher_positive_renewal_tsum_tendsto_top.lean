-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_positive_renewal_tsum_tendsto_top
-- name    : AvramDividend.Classical.esscher_positive_renewal_tsum_tendsto_top
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:38:35.333836+00:00
-- url     : https://prove2.me/theorems/eed0b8cf-1a27-4e4c-8c20-71634e1d187a
-- title:
--   Diverging Esscher renewal first term forces the full positive convolution series to diverge
-- statement:
--   For the bounded-variation Esscher renewal representation, the positive shifted convolution-power sum dominates its first term. If the canonical positive tail kernel diverges at the origin, every positive renewal density formed from summable nonnegative powers does likewise. This is the precise series step connecting canonical jump tails to the derivative of the q-scale function.
-- source:
--   Summable positive series bound in pinned Mathlib Topology.Algebra.InfiniteSum.Order, and ordinary atTop filter comparison.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Mathlib.Topology.Algebra.InfiniteSum.Order
import Mathlib.Topology.Algebra.Order.Field

open AvramDividend.Classical Filter Topology
open scoped BigOperators

namespace AvramDividend.Classical

/-- A positive renewal series with a diverging first convolution term diverges at the origin. -/
theorem esscher_positive_renewal_tsum_tendsto_top
    (κ : ℝ → ℝ) (F : ℝ → ℕ → ℝ)
    (hκ : Tendsto κ (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop)
    (hsum : ∀ x : ℝ, 0 < x → Summable (F x))
    (hfirst : ∀ x : ℝ, 0 < x → F x 0 = κ x)
    (hnonneg : ∀ x : ℝ, 0 < x → ∀ n : ℕ, 0 ≤ F x n) :
    Tendsto (fun x : ℝ => ∑' n : ℕ, F x n)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) atTop := by sorry

end AvramDividend.Classical
