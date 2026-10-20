-- Prove2me | Theorems.Thm_BundleSearch_MatureNew_proposition_1_iii
-- name    : BundleSearch.MatureNew.proposition_1_iii
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-20T02:26:12.116111+00:00
-- url     : https://prove2.me/theorems/97177f7e-2001-404a-b94d-021845fdab5e
-- title:
--   Proposition 1 (iii), p. 10 — new product when c ≤ 1/32
-- statement:
--   For $0\le c\le1/32$, price $p_2=1/2$ maximizes new-product revenue over nonnegative prices. Half of the customers buy after learning their valuations, and the revenue is $1/4$:
--
--   $$p_2^*=1/2,\qquad D_N(c,p_2^*)=1/2,\qquad R_N(c,p_2^*)=1/4.$$
--
--   This is the low-cost part of the separate-selling benchmark. The statement does not claim that $1/2$ is the only optimal price at the boundary $c=1/32$.
-- source:
--   Wu, Jin & Chen, Managing Customer Search via Product Bundling, SSRN working paper 3692871 (version of 2022-01-17), p. 10, Proposition 1(iii)

import Mathlib
import Definitions.Def_BundleSearch_MatureNew_Model

namespace BundleSearch.MatureNew

/-- Proposition 1(iii), p. 10: at low search cost, price 1/2 is optimal with half the
customers buying after search. -/
theorem proposition_1_iii (c : ℝ) (hc : 0 ≤ c) (hc' : c ≤ 1 / 32) :
    IsGreatest (revenueNew c '' Set.Ici (0 : ℝ)) (1 / 4) ∧
    demandNew c (1 / 2) = 1 / 2 ∧ revenueNew c (1 / 2) = 1 / 4 := by sorry

end BundleSearch.MatureNew
