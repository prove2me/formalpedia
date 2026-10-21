-- Prove2me | Theorems.Thm_BundleSearch_MatureNew_proposition_1_i
-- name    : BundleSearch.MatureNew.proposition_1_i
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:26:06.795869+00:00
-- url     : https://prove2.me/theorems/85e1269d-93b5-4515-b03e-e4edec819d1e
-- title:
--   Proposition 1 (i), p. 9 — new product when c > 1/8
-- statement:
--   Suppose search costs more than $1/8$. For a new product sold at nonnegative price, $p_2=1/2$ maximizes revenue. At this price all customers buy and the seller earns $1/2$:
--
--   $$c>1/8:\qquad p_2^*=1/2,\quad D_N(c,p_2^*)=1,\quad R_N(c,p_2^*)=1/2.$$
--
--   The optimality claim ranges over every nonnegative price, without claiming that this price is unique. It is the high-cost part of the separate-selling benchmark.
-- source:
--   Wu, Jin & Chen, Managing Customer Search via Product Bundling, SSRN working paper 3692871 (version of 2022-01-17), p. 9, Proposition 1(i)

import Mathlib
import Definitions.Def_BundleSearch_MatureNew_Model

namespace BundleSearch.MatureNew

/-- Proposition 1(i), p. 9: at search cost above 1/8, all buy without search at price 1/2. -/
theorem proposition_1_i (c : ℝ) (hc : 1 / 8 < c) :
    IsGreatest (revenueNew c '' Set.Ici (0 : ℝ)) (1 / 2) ∧
    demandNew c (1 / 2) = 1 ∧ revenueNew c (1 / 2) = 1 / 2 := by sorry

end BundleSearch.MatureNew
