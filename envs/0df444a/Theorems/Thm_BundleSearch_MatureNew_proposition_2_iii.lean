-- Prove2me | Theorems.Thm_BundleSearch_MatureNew_proposition_2_iii
-- name    : BundleSearch.MatureNew.proposition_2_iii
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-20T02:26:17.616923+00:00
-- url     : https://prove2.me/theorems/80aa2dc5-1d8b-4af9-9dcd-a81efdb37dcd
-- title:
--   Proposition 2, third case, p. 13 — higher-cost optimal bundle
-- statement:
--   For $c>1/32$, bundle price $p_B=3/4$ maximizes revenue over every nonnegative bundle price, and the resulting revenue is $9/16$:
--
--   $$p_B^*=3/4,\qquad R_B(c,p_B^*)=9/16.$$
--
--   This is the third case of Proposition 2. It provides the bundle-revenue level used when comparing bundling with separate selling at and above the threshold in Theorem 1.
-- source:
--   Wu, Jin & Chen, Managing Customer Search via Product Bundling, SSRN working paper 3692871 (version of 2022-01-17), p. 13, Proposition 2, case c > 1/32

import Mathlib
import Definitions.Def_BundleSearch_MatureNew_Model

namespace BundleSearch.MatureNew

/-- Proposition 2, third case, p. 13: at higher search costs, bundle price 3/4 earns 9/16. -/
theorem proposition_2_iii (c : ℝ) (hc : 1 / 32 < c) :
    IsGreatest (bundleRevenue c '' Set.Ici (0 : ℝ)) (9 / 16) ∧
    bundleRevenue c (3 / 4) = 9 / 16 := by sorry

end BundleSearch.MatureNew
