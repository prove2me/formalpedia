-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_F_two_pos
-- name    : DataTrackComp.Surplus.F_two_pos
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:25:34.783306+00:00
-- url     : https://prove2.me/theorems/28513449-493c-485e-9549-645ec80abcb4
-- title:
--   Proof of Claim 23, p. OA-25 — m_L > 2, and F(2) = Γ(X̄∗(2), 2) > 0
-- statement:
--   This item has two parts.
--
--   1. $m_L>2$: there is $m'>2$ such that $\mathbf G(\mu)$ has an interior pure-strategy Nash equilibrium for every $\mu\in(0,m']$.
--   2. $F(2)>0$: for every $x$ with $0<x<1/2$ and $N(x,2)=0$,
--   $$\Gamma(x,2)>0.$$
--
--   By (C.4) and Claim 22, the root of $N(\cdot,2)$ in $(0,1/2)$ is $\bar X^*(2)\approx0.2423$. So the second part is $F(2)=\Gamma(\bar X^*(2),2)\approx0.06126>0$. With continuity and the absence of roots, this gives $F>0$ on $(0,m_L)$.
--
--   **Formalization Note.** The paper attributes $m_L>2$ to Remark 1 ($m_L\approx3.98$).
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-25 (PDF 60), proof of Claim 23, step (iii)

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_ReducedGame
import Definitions.Def_DataTrackComp_Surplus_AppendixC

namespace DataTrackComp.Surplus

theorem F_two_pos :
    InInteriorRegime 2 ∧ ∀ x : ℝ, 0 < x → x < 1 / 2 → N x 2 = 0 → 0 < Gam x 2 := by sorry

end DataTrackComp.Surplus
