-- Prove2me | Theorems.Thm_AdvanceSales_Pricing_proposition_21
-- name    : AdvanceSales.Pricing.proposition_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:56.405743+00:00
-- url     : https://prove2.me/theorems/9da9d617-19cc-4ab4-9f35-96e2d3b8d62f
-- title:
--   Proposition 21 — comparison of the regional candidate profits
-- statement:
--   For $k>0$ and $v>1$, compare the three candidate profits from Proposition 20. Whenever $v-k\ge1$,
--
--   $$\pi_4<\pi_2.$$
--
--   For every $v>1$, $\pi_3\le\pi_2$, with strict inequality unless $v=e^{W+k+1}$. These comparisons select the best available candidate in the low-value regimes.
--
--   **Formalization Note** The printed unrestricted first inequality fails when $v-k<1$. The printed strict second inequality has equality at $v=e^{W+k+1}$; the paper's proof itself establishes the non-strict bound.
-- source:
--   Glazer, Hassin, Nowik, How Advance Sales Can Reduce Profits, arXiv:1912.02869v2, pp. 39–40, Proposition 21 and (49)

import Mathlib
import Definitions.Def_AdvanceSales_Pricing_Setting

namespace AdvanceSales.Pricing

theorem proposition_21 (v k : ℝ) (hk : 0 < k) (hv : 1 < v) :
    (1 ≤ v - k → pi4 v k < pi2 v) ∧
    pi3 v k ≤ pi2 v ∧
    (v ≠ Real.exp (Wk k + k + 1) → pi3 v k < pi2 v) := by sorry

end AdvanceSales.Pricing
