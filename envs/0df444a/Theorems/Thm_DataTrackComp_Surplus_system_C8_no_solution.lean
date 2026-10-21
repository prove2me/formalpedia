-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_system_C8_no_solution
-- name    : DataTrackComp.Surplus.system_C8_no_solution
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:29.045608+00:00
-- url     : https://prove2.me/theorems/94706560-676e-4438-9277-df76bf37a1d0
-- title:
--   Proof of Claim 23, p. OA-25 — system (C.8), Q1 = Q2 = 0, has no solution with 0 < w < 1 and z > 0
-- statement:
--   For all real $w,z$ with $0<w<1$ and $z>0$,
--   $$\neg\big(Q_1(w,z)=0\ \wedge\ Q_2(w,z)=0\big).\qquad(C.8)$$
--
--   The paper solves (C.8) with a Gröbner basis. Its real solutions are $(0,0)$, $\pm(1,1)$ and $\pm(1.32385,0.589199)$ (footnote 41), and none lies in the region. Hence $F(m)=\Gamma(\bar X^*(m),m)$ has no root on $(0,m_L)$.
--
--   **Formalization Note.** The region $0<w<1$, $z>0$ is the one the paper verifies on p. OA-25. The last line of p. OA-24 reads "$w>0$ and $w>z$", which cannot hold, since $z^2-w^2=m>0$; it is a typo.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-25 (PDF 60), proof of Claim 23, (C.8) and footnote 41

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_AppendixC

namespace DataTrackComp.Surplus

theorem system_C8_no_solution (w z : ℝ) (hw0 : 0 < w) (hw1 : w < 1) (hz : 0 < z) :
    ¬ (Q1 w z = 0 ∧ Q2 w z = 0) := by sorry

end DataTrackComp.Surplus
