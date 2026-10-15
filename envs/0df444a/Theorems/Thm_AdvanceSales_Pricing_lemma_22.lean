-- Prove2me | Theorems.Thm_AdvanceSales_Pricing_lemma_22
-- name    : AdvanceSales.Pricing.lemma_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:55.769511+00:00
-- url     : https://prove2.me/theorems/980939f5-492a-4e66-8304-cec894133da1
-- title:
--   Lemma 22 — the second-period candidate lies in Region 2
-- statement:
--   If $k>0$ and $1<v\le e^{W+k+1}$, then the candidate $p_2=v-\ln v/(1-1/v)$ lies between the two price borders of Region 2:
--
--   $$v-k-1\le p_2\le v-1.$$
--
--   This makes the second-period regional maximum attainable in the first regime of Theorem 4.
--
--   **Formalization Note** The printed lower endpoint $v=1$ is excluded because the printed fraction is $0/0$ there; the paper uses its limit.
-- source:
--   Glazer, Hassin, Nowik, How Advance Sales Can Reduce Profits, arXiv:1912.02869v2, pp. 40–41, Lemma 22

import Mathlib
import Definitions.Def_AdvanceSales_Pricing_Setting

namespace AdvanceSales.Pricing

theorem lemma_22 (v k : ℝ) (hk : 0 < k) (hv : 1 < v)
    (hupper : v ≤ Real.exp (Wk k + k + 1)) :
    v - k - 1 ≤ p2 v ∧ p2 v ≤ v - 1 := by sorry

end AdvanceSales.Pricing
