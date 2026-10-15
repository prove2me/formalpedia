-- Prove2me | Theorems.Thm_CrowdfundRM_Triangular_corollary_2
-- name    : CrowdfundRM.Triangular.corollary_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T06:50:18.330922+00:00
-- url     : https://prove2.me/theorems/4c14d64f-54ce-46bc-bb0b-6d2ece0847f2
-- title:
--   Corollary 2, p. 12 — the total number of pledges n(p,T) has the closed form (17)
-- statement:
--   Consider a campaign satisfying the standing assumptions, a pledge level $p$ and a duration $T\ge0$. The total number of pledges $n(p,T)=n^p_i(T,p,T)+n^p_h(T,p,T)$, computed from (5) and (11), equals
--   $$n(p,T)=k\hat I\Bigl(e^{-kT}\int_0^T dx\,e^{kx}\bar F_i(pe^{rx})\,e^{\Lambda_h q p\int_0^x \bar F_h(pe^{ry})dy}\Bigr).\qquad(17)$$
--
--   Formula (17) is the objective of the creator's problem (18) in one integral; the reduced revenue functions $R_i$ (22) and $R_h$ (27) are read off from it.
-- source:
--   Zhang, Savin, Veeraraghavan, Revenue Management in Crowdfunding, SSRN 3065267 (manuscript of May 26, 2021), p. 12, Corollary 2, (17)

import Mathlib
import Definitions.Def_CrowdfundRM_Triangular_Setting

namespace CrowdfundRM.Triangular
theorem corollary_2 (M : Campaign) (hM : M.Standing) (p T : ℝ) (hT : 0 ≤ T) :
    M.ntot p T = M.nCor2 p T := by sorry
end CrowdfundRM.Triangular
