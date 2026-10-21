-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_eq_C4
-- name    : DataTrackComp.Surplus.eq_C4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:20.946977+00:00
-- url     : https://prove2.me/theorems/975e38d1-8048-4c16-a107-5f2891ff8512
-- title:
--   Proof of Claim 22, p. OA-22, (C.4) — the forward-looking price dispersion X̄∗(m) solves N(x, m) = 0
-- statement:
--   Let $\bar u>0$ and $0<m<m_L$. For every equilibrium of the forward-looking setting with product-1 prices $p^{A*}_1,p^{B*}_1$, the dispersion $\bar X^*(m)=p^{B*}_1-p^{A*}_1+1/2$ is a root of
--   $$N(x,m)=m^2-4m+20x^2+12mx-10x-\sqrt{2x(2x+m)}\,(1-2x).\qquad(C.4)$$
--
--   Together with the strict convexity of $N(\cdot,m)$, this identifies $\bar X^*(m)$ as the unique root of $N(\cdot,m)$ in $[0,1]$ (Claim 22). The proofs of Claims 22 and 23 use this characterization.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-22 (PDF 57), proof of Claim 22, (C.4) (citing Step 3 of the proof of Claim 44)

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_DataTrackComp_Surplus_ReducedGame
import Definitions.Def_DataTrackComp_Surplus_AppendixC

namespace DataTrackComp.Surplus

theorem eq_C4 (ubar m : ℝ) (hu : 0 < ubar) (hm : 0 < m) (hmL : InInteriorRegime m)
    (E : Assessment) (hE : IsEquilibrium .forward ubar m E) :
    N (E.pB - E.pA + 1 / 2) m = 0 := by sorry

end DataTrackComp.Surplus
