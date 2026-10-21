-- Prove2me | Theorems.Thm_DataTrackComp_Surplus_remark_1
-- name    : DataTrackComp.Surplus.remark_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:24:26.564853+00:00
-- url     : https://prove2.me/theorems/6076a539-346c-4b2d-a4bf-3488efa4d200
-- title:
--   Remark 1, p. OA-19 — G(4) admits no pure-strategy Nash equilibrium, and m_L < 4
-- statement:
--   The following two statements hold.
--
--   1. The reduced game $\mathbf G(4)$ admits no pure-strategy Nash equilibrium.
--   2. $m_L<4$, where $m_L=\sup\{m'>0:(0,m']\subseteq\mathcal E\}$ (B.32). Stated without a supremum: there is $b<4$ such that every $m'$ for which $\mathbf G(\mu)$ has an interior PSNE for all $\mu\in(0,m']$ satisfies $m'\le b$.
--
--   The bound $m_L<4$ is used in Claim 22: $N(0,m)=m(m-4)<0$ on $(0,m_L)$.
--
--   **Formalization Note.** Remark 1 also states $4<m_H$ and the numerical values $m_L\approx3.98$, $m_H\approx4.02$. Neither $m_H$ nor these approximations are formalized, because the proof of Theorem 2 does not use them.
-- source:
--   Bimpikis, Morgenstern & Saban, Data Tracking under Competition, authors' manuscript with online appendix (Operations Research, doi:10.1287/opre.2023.2489; PDF of 2023-05-04), p. OA-19 (PDF 54), Remark 1 (proof in F.2, pp. OA-65–OA-66)

import Mathlib
import Definitions.Def_DataTrackComp_Surplus_ReducedGame

namespace DataTrackComp.Surplus

theorem remark_1 :
    (¬ ∃ pA pB : ℝ, IsPSNE 4 pA pB) ∧
    ∃ b : ℝ, b < 4 ∧ ∀ m' : ℝ, (∀ μ ∈ Set.Ioc (0 : ℝ) m', HasInteriorPSNE μ) → m' ≤ b := by sorry

end DataTrackComp.Surplus
