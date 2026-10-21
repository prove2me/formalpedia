-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_claim_23
-- name    : DataTrackComp.Surplus.claim_23
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:29.316141+00:00
-- url     : https://prove2.me/theorems/5050fd23-821d-4970-a9eb-40f300fbaeab
-- title:
--   Claim 23, p. OA-22 — for 0 < m < m_L, consumer surplus is higher with forward-looking than with myopic consumers
-- statement:
--   Let $\bar u>0$ and $0<m<m_L$. For every equilibrium of the forward-looking setting and every equilibrium of the myopic setting,
--   $$CS^{FL}(m)>CS^M(m).$$
--
--   Combined with Claim 20 ($CS^M>CS^R$), this gives the chain $CS^{FL}>CS^M>CS^R$ and hence Theorem 2.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-22 (PDF 57), Claim 23

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_DataTrackComp_Surplus_ReducedGame

namespace DataTrackComp.Surplus

theorem claim_23 (ubar m : ℝ) (hu : 0 < ubar) (hm : 0 < m) (hmL : InInteriorRegime m)
    (EF EM : Assessment) (hF : IsEquilibrium .forward ubar m EF) (hM : IsEquilibrium .myopic ubar m EM) :
    consumerSurplus .myopic ubar m EM < consumerSurplus .forward ubar m EF := by sorry

end DataTrackComp.Surplus
