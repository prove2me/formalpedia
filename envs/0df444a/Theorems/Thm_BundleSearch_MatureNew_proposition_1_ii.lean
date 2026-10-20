-- Prove2me | Theorems.Thm_BundleSearch_MatureNew_proposition_1_ii
-- name    : BundleSearch.MatureNew.proposition_1_ii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:26:14.380393+00:00
-- url     : https://prove2.me/theorems/57cf0601-cb50-4740-b3a8-a3006bd2ab99
-- title:
--   Proposition 1 (ii), p. 10 — new product when 1/32 < c ≤ 1/8
-- statement:
--   For $1/32<c\le1/8$, setting the new-product price at $\sqrt{2c}$ maximizes revenue over all nonnegative prices. Every customer buys without search there, so demand is one and revenue equals the price:
--
--   $$p_2^*=\sqrt{2c},\qquad D_N(c,p_2^*)=1,\qquad R_N(c,p_2^*)=\sqrt{2c}.$$
--
--   This gives the middle search-cost regime of the separate-selling benchmark. Optimality is asserted without uniqueness.
-- source:
--   Wu, Jin & Chen, Managing Customer Search via Product Bundling, SSRN working paper 3692871 (version of 2022-01-17), p. 10, Proposition 1(ii)

import Mathlib
import Definitions.Def_BundleSearch_MatureNew_Model

namespace BundleSearch.MatureNew

/-- Proposition 1(ii), p. 10: the search-deterring price sqrt(2c) is optimal. -/
theorem proposition_1_ii (c : ℝ) (hc : 1 / 32 < c) (hc' : c ≤ 1 / 8) :
    IsGreatest (revenueNew c '' Set.Ici (0 : ℝ)) (Real.sqrt (2 * c)) ∧
    demandNew c (Real.sqrt (2 * c)) = 1 ∧
    revenueNew c (Real.sqrt (2 * c)) = Real.sqrt (2 * c) := by sorry

end BundleSearch.MatureNew
