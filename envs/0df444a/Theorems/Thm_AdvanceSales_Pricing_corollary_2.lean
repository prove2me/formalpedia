-- Prove2me | Theorems.Thm_AdvanceSales_Pricing_corollary_2
-- name    : AdvanceSales.Pricing.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:45:00.759858+00:00
-- url     : https://prove2.me/theorems/71e06bac-09a4-4866-a4c4-51111df67d75
-- title:
--   Corollary 2 — profit increases with price in Region 3
-- statement:
--   Fix $v$ and $k>0$. For nonnegative prices $p<p'$ whose equilibria $(x,y)$ and $(x',y')$ both have positive arrival rates in both periods, the seller's expected profit increases:
--
--   $$p(1-e^{-(x+y)})<p'(1-e^{-(x'+y')}).$$
--
--   This rules out the interior of the mixed-arrival region as a profit-maximizing price.
--
--   **Formalization Note** The nonnegative price convention is explicit; Region 3 is encoded by positive rates at both prices.
-- source:
--   Glazer, Hassin, Nowik, How Advance Sales Can Reduce Profits, arXiv:1912.02869v2, p. 13, Corollary 2

import Mathlib
import Definitions.Def_AdvanceSales_Pricing_Setting

namespace AdvanceSales.Pricing

theorem corollary_2 (v k : ℝ) (hk : 0 < k) :
    ∀ p p' x y x' y' : ℝ, 0 ≤ p → 0 ≤ p' → p < p' →
      IsEq v k p x y → IsEq v k p' x' y' →
      0 < x → 0 < y → 0 < x' → 0 < y' →
      profit p x y < profit p' x' y' := by sorry

end AdvanceSales.Pricing
