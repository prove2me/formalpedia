-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_gamma_eq_J1_div_J2
-- name    : DataTrackComp.Surplus.gamma_eq_J1_div_J2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:46.741881+00:00
-- url     : https://prove2.me/theorems/4a766f20-b78a-487b-816e-faebc1e5f4c4
-- title:
--   Proof of Claim 23, p. OA-24 — Γ = J1/J2 on 0 < x < x̃(m), J2 > 0, and the change of variables (C.7)
-- statement:
--   This item collects three algebraic facts from the proof of Claim 23.
--
--   1. $J_2(x,m)>0$ for all $x,m>0$.
--   2. For $m>0$ and $0<x<\tilde x(m)$,
--   $$\Gamma(x,m)=\frac{J_1(x,m)}{J_2(x,m)}.$$
--   3. For $0<w<z$, the substitution $x=w^2/2$, $m=z^2-w^2>0$ (so that $\sqrt{2x(2x+m)}=wz$) gives
--   $$J_1\!\left(\tfrac{w^2}{2},z^2-w^2\right)=(w-z)\,Q_1(w,z),\qquad N\!\left(\tfrac{w^2}{2},z^2-w^2\right)=Q_2(w,z).\qquad(C.7)$$
--
--   Together they turn the question whether $\Gamma$ and $N$ have a common zero into the polynomial system (C.8).
--
--   **Formalization Note.** $\Gamma$ uses $Z=\psi/\psi_x$ with $\psi_x$ the derivative of $\psi(\cdot,m)$. On $0<x<\tilde x(m)$ this is the derivative of the first branch of (B.2), as in the paper's closed form (F.4).
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-24 (PDF 59), proof of Claim 23, Γ = J1/J2 and (C.7)

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_ReducedGame
import Definitions.Def_DataTrackComp_Surplus_AppendixC

namespace DataTrackComp.Surplus

theorem gamma_eq_J1_div_J2 :
    (∀ x m : ℝ, 0 < x → 0 < m → 0 < J2 x m) ∧
    (∀ x m : ℝ, 0 < m → 0 < x → x < xtilde m → Gam x m = J1 x m / J2 x m) ∧
    (∀ w z : ℝ, 0 < w → w < z →
      J1 (w ^ 2 / 2) (z ^ 2 - w ^ 2) = (w - z) * Q1 w z ∧ N (w ^ 2 / 2) (z ^ 2 - w ^ 2) = Q2 w z) := by sorry

end DataTrackComp.Surplus
