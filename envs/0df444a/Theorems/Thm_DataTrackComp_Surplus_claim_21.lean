-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_claim_21
-- name    : DataTrackComp.Surplus.claim_21
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:32.256992+00:00
-- url     : https://prove2.me/theorems/2f05c9e6-1069-473c-a73d-5f1cf161be04
-- title:
--   Claim 21, p. OA-21 — consumer surplus in the forward-looking setting, closed form (C.3)
-- statement:
--   Let $\bar u>0$ and $0<m<m_L$. Take any equilibrium of the forward-looking setting, with product-1 prices $p^{A*}_1,p^{B*}_1$. Let $\bar X^*=p^{B*}_1-p^{A*}_1+1/2$ and $\bar\theta^*=\bar\theta(\bar X^*,m)$. Then its aggregate consumer surplus is
--   $$CS^{FL}(m)=\bar u-\tfrac14-p^{B*}_1+\tfrac12(\bar X^*)^2+\tfrac12m\bar X^*(1-\bar\theta^*)^2+\tfrac16m^2(1-\bar\theta^*)^3.\qquad(C.3)$$
--
--   This is the surplus formula compared with $CS^M$ in Claim 23.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-21 (PDF 56), Claim 21, (C.3)

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_DataTrackComp_Surplus_ReducedGame

namespace DataTrackComp.Surplus

theorem claim_21 (ubar m : ℝ) (hu : 0 < ubar) (hm : 0 < m) (hmL : InInteriorRegime m)
    (E : Assessment) (hE : IsEquilibrium .forward ubar m E) :
    consumerSurplus .forward ubar m E =
      ubar - 1 / 4 - E.pB + (1 / 2) * (E.pB - E.pA + 1 / 2) ^ 2 +
        (1 / 2) * m * (E.pB - E.pA + 1 / 2) * (1 - thetaBar (E.pB - E.pA + 1 / 2) m) ^ 2 +
        (1 / 6) * m ^ 2 * (1 - thetaBar (E.pB - E.pA + 1 / 2) m) ^ 3 := by sorry

end DataTrackComp.Surplus
