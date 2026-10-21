-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_claim_22
-- name    : DataTrackComp.Surplus.claim_22
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:39.645988+00:00
-- url     : https://prove2.me/theorems/00bd925d-9e0d-4411-9bab-d68ec3cfa460
-- title:
--   Claim 22, p. OA-22 — X̄∗(m) is continuous in m and 0 < X̄∗(m) < 1/2 for 0 < m < m_L
-- statement:
--   For $0<m<m_L$, let $\bar X^*(m)=p^{B*}_1(m)-p^{A*}_1(m)+1/2$ be the product-1 price dispersion of the forward-looking equilibrium. The claim has two parts.
--
--   1. For every $\bar u>0$ and every forward-looking equilibrium,
--   $$0<\bar X^*(m)<\tfrac12.$$
--   2. $\bar X^*$ is continuous in $m$: there is a function $f$ that is continuous on $\{m>0: m<m_L\}$ and equals the dispersion of every forward-looking equilibrium, for every $\bar u>0$, at every such $m$.
--
--   Continuity of $F(m)=\Gamma(\bar X^*(m),m)$ in Claim 23 rests on this claim.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-22 (PDF 57), Claim 22

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_Game
import Definitions.Def_DataTrackComp_Surplus_ReducedGame

namespace DataTrackComp.Surplus

theorem claim_22 :
    (∀ ubar m : ℝ, 0 < ubar → 0 < m → InInteriorRegime m →
      ∀ E : Assessment, IsEquilibrium .forward ubar m E →
        0 < E.pB - E.pA + 1 / 2 ∧ E.pB - E.pA + 1 / 2 < 1 / 2) ∧
    ∃ f : ℝ → ℝ, ContinuousOn f {m : ℝ | 0 < m ∧ InInteriorRegime m} ∧
      ∀ ubar m : ℝ, 0 < ubar → 0 < m → InInteriorRegime m →
        ∀ E : Assessment, IsEquilibrium .forward ubar m E → E.pB - E.pA + 1 / 2 = f m := by sorry

end DataTrackComp.Surplus
