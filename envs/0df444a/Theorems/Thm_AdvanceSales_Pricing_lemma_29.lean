-- Prove2me | Theorems.Thm_AdvanceSales_Pricing_lemma_29
-- name    : AdvanceSales.Pricing.lemma_29
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:44:52.719469+00:00
-- url     : https://prove2.me/theorems/ab2a9060-2369-49da-9e6b-8e3dc8093927
-- title:
--   Lemma 29 — the first-period candidate lies in Region 4
-- statement:
--   Let $k>0$ and let $v(k)$ be the border between mixed and early-only arrivals. If $v\ge k+v(k)$, then $p_4$ lies in Region 4, whose price borders are
--
--   $$0\le p_4\le v-v(k).$$
--
--   Moreover $v_f\ge k+v(k)$. Thus above the switching threshold the first-period candidate is feasible in its intended region.
--
--   **Formalization Note** The second inequality is asserted in the paper and supported there by Figure 20; it is retained as a proof target.
-- source:
--   Glazer, Hassin, Nowik, How Advance Sales Can Reduce Profits, arXiv:1912.02869v2, pp. 44–45, Lemma 29

import Mathlib
import Definitions.Def_AdvanceSales_Pricing_Setting

namespace AdvanceSales.Pricing

theorem lemma_29 (v k : ℝ) (hk : 0 < k) :
    (k + vOf k ≤ v → 0 ≤ p4 v k ∧ p4 v k ≤ v - vOf k) ∧
    k + vOf k ≤ vf k := by sorry

end AdvanceSales.Pricing
