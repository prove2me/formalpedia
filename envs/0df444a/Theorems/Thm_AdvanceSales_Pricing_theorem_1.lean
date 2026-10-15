-- Prove2me | Theorems.Thm_AdvanceSales_Pricing_theorem_1
-- name    : AdvanceSales.Pricing.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:52.731681+00:00
-- url     : https://prove2.me/theorems/ab9d6ba4-fb08-402e-bff2-e2abd5e891c7
-- title:
--   Theorem 1 — aggregate arrivals increase with price in Region 3
-- statement:
--   Let $v$ and $k>0$ be fixed. If two nonnegative prices $p<p'$ both induce Region 3 equilibria, with positive early and late arrival rates $(x,y)$ and $(x',y')$, then
--
--   $$x+y<x'+y'.$$
--
--   Thus, while both arrival times are used, increasing the price strictly raises the total arrival rate. This is the paper's central monotonicity result.
--
--   **Formalization Note** Region 3 is identified by both equilibrium rates being positive, as in Table 1.
-- source:
--   Glazer, Hassin, Nowik, How Advance Sales Can Reduce Profits, arXiv:1912.02869v2, p. 12, Theorem 1

import Mathlib
import Definitions.Def_AdvanceSales_Pricing_Setting

namespace AdvanceSales.Pricing

theorem theorem_1 (v k : ℝ) (hk : 0 < k) :
    ∀ p p' x y x' y' : ℝ, 0 ≤ p → 0 ≤ p' → p < p' →
      IsEq v k p x y → IsEq v k p' x' y' →
      0 < x → 0 < y → 0 < x' → 0 < y' → x + y < x' + y' := by sorry

end AdvanceSales.Pricing
