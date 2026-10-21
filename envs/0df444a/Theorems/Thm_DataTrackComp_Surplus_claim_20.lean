-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_claim_20
-- name    : DataTrackComp.Surplus.claim_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:25.539532+00:00
-- url     : https://prove2.me/theorems/1aaf244d-c10b-4d06-b94d-edbd4d6cb2a2
-- title:
--   Claim 20, p. OA-20 — CS^R = ū − 5/8 + m/8, CS^M from (C.1), and CS^M > CS^R for m ∈ (0, m_L)
-- statement:
--   Let $\bar u>0$ and $m>0$. The equilibrium aggregate consumer surplus of every equilibrium of the restricted setting, and of every equilibrium of the myopic setting, is
--   $$CS^R(m)=\bar u-\tfrac58+\tfrac m8,\qquad CS^M(m)=\begin{cases}\bar u-\tfrac58+\tfrac{m}{144}(27-m),&m\le6,\\ \bar u+\tfrac14,&\text{otherwise.}\end{cases}\qquad(C.1)$$
--   Moreover, if $m<m_L$, then $CS^R<CS^M$ for every restricted equilibrium and every myopic equilibrium.
--
--   This is the first half of Theorem 2: data tracking with myopic consumers raises consumer surplus.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-20 (PDF 55), Claim 20, (C.1)

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_DataTrackComp_Surplus_ReducedGame

namespace DataTrackComp.Surplus

theorem claim_20 (ubar m : ℝ) (hu : 0 < ubar) (hm : 0 < m) :
    (∀ E : Assessment, IsEquilibrium .restricted ubar m E →
      consumerSurplus .restricted ubar m E = ubar - 5 / 8 + m / 8) ∧
    (∀ E : Assessment, IsEquilibrium .myopic ubar m E →
      consumerSurplus .myopic ubar m E =
        if m ≤ 6 then ubar - 5 / 8 + m / 144 * (27 - m) else ubar + 1 / 4) ∧
    (InInteriorRegime m → ∀ ER EM : Assessment, IsEquilibrium .restricted ubar m ER →
      IsEquilibrium .myopic ubar m EM →
      consumerSurplus .restricted ubar m ER < consumerSurplus .myopic ubar m EM) := by sorry

end DataTrackComp.Surplus
