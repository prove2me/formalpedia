-- Prove2me | Theorems.Thm_EngagementOpt_Misalign_thm_4_1_step_q
-- name    : EngagementOpt.Misalign.thm_4_1_step_q
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:51.195664+00:00
-- url     : https://prove2.me/theorems/b397a3ff-dc1b-4b79-8cea-c8fe889d140c
-- title:
--   Proof of Theorem 4.1, p. 16 — if $p_T\le p_S$ and $g_T(\omega_T)>g_T(\omega_S)$, then $q_T>q_S$
-- statement:
--   This is the first step of the proof of Theorem 4.1.
--
--   Let $\omega_S=(p_S,q_S,\bar v_S)$ and $\omega_T=(p_T,q_T,\bar v_T)$ be two points of $\Omega=[0,1)\times[0,1)\times\mathbb R_+$, and let $g_T(\omega)=\frac1{1-q}+\frac{p}{1-p}$. If
--   $$p_T\le p_S\qquad\text{and}\qquad g_T(\omega_T)>g_T(\omega_S),$$
--   then
--   $$q_T>q_S.$$
--
--   In words: if the engagement-maximizing content is not more moreish, its higher engagement must come from a longer span. No maximizer hypothesis is needed for this step.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 16, proof of Theorem 4.1 (first display)

import Mathlib
import Definitions.Def_EngagementOpt_Misalign_Model

namespace EngagementOpt.Misalign

/-- Proof of Theorem 4.1, p. 16: for `ω_S, ω_T ∈ Ω`, if `p_T ≤ p_S` and
`g_T(ω_T) > g_T(ω_S)`, then `q_T > q_S`. -/
theorem thm_4_1_step_q (ωS ωT : Params) (hS : InOmega ωS) (hT : InOmega ωT)
    (hp : ωT.p ≤ ωS.p) (hgT : gT ωS < gT ωT) :
    ωS.q < ωT.q := by sorry

end EngagementOpt.Misalign
