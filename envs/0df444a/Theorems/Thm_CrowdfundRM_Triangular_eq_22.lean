-- Prove2me | Theorems.Thm_CrowdfundRM_Triangular_eq_22
-- name    : CrowdfundRM.Triangular.eq_22
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:22.250763+00:00
-- url     : https://prove2.me/theorems/1a4d000a-82dd-4e02-bf8c-6b09cc411319
-- title:
--   (22), p. 14 — without herding backers the total pledged revenue π(p,T) equals R_i(p,T)
-- statement:
--   Consider a campaign satisfying the standing assumptions with no herding backers, $\Lambda_h=0$. For every pledge level $p$ and duration $T\ge0$ the revenue $\pi(p,T)=p\,n(p,T)$ equals
--   $$R_i(p,T)=k\hat I p e^{-kT}\int_0^T dx\,e^{kx}\bar F_i(pe^{rx}).\qquad(22)$$
--
--   This identity reduces the no-herding optimization problems (Proposition 4 and Proposition 7(a)) to the explicit function $R_i$, which depends only on the independent backers' valuation law.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), §4, p. 14, (22)

import Mathlib
import Definitions.Def_CrowdfundRM_Triangular_Setting

namespace CrowdfundRM.Triangular
theorem eq_22 (M : Campaign) (hM : M.Standing) (hLh : M.Lh = 0) (p T : ℝ) (hT : 0 ≤ T) :
    M.revenue p T = M.Ri p T := by sorry
end CrowdfundRM.Triangular
