-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_claim_12
-- name    : DataTrackComp.Surplus.claim_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:24.18077+00:00
-- url     : https://prove2.me/theorems/ca63bfb5-48e4-4922-a3d9-2c17ed8412e7
-- title:
--   Claim 12, p. OA-17 — firm A's best response in G(m): all of S_A at p^B_1 = −1/2; otherwise unique, solving p^A_1 = Z(X̄, m)
-- statement:
--   Let $m>0$ and $p^B_1\in S_B=[-1/2,1]$, and let $BR^A(p^B_1,m)\subseteq S_A$ be firm A's best responses in $\mathbf G(m)$. Then the following hold.
--
--   1. $BR^A(-1/2,m)=S_A$.
--   2. If $p^B_1>-1/2$, firm A has exactly one best response. Equation (B.28),
--   $$p^A_1=Z\!\left(\bar X(p^A_1,p^B_1),m\right),\qquad Z(x,m)=\frac{\psi(x,m)}{\psi_x(x,m)},\qquad(B.28),(B.29)$$
--   has exactly one solution $p^A_1\in S_A$, and the best response solves it.
--
--   In the proof of Theorem 2, this yields $p^{A*}_1(m)=Z(\bar X^*(m),m)$. That identity turns the lower bound $F(m)$ on $CS^{FL}-CS^M$ into $\Gamma(\bar X^*(m),m)$.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-17 (PDF 52), Claim 12, (B.28)–(B.29), footnote 34

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_DataTrackComp_Surplus_ReducedGame

namespace DataTrackComp.Surplus

theorem claim_12 (m pB : ℝ) (hm : 0 < m) (hpB : pB ∈ SB) :
    (pB = -1 / 2 → ∀ a : ℝ, IsBestRespA m pB a ↔ a ∈ SA) ∧
    (-1 / 2 < pB →
      (∃! a : ℝ, IsBestRespA m pB a) ∧
      (∃! a : ℝ, a ∈ SA ∧ a = Z (Xbar a pB) m) ∧
      ∀ a : ℝ, IsBestRespA m pB a → a = Z (Xbar a pB) m) := by sorry

end DataTrackComp.Surplus
