-- Prove2me | Theorems.Thm_EngagementOpt_Misalign_thm_4_1_step_v
-- name    : EngagementOpt.Misalign.thm_4_1_step_v
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:58.402741+00:00
-- url     : https://prove2.me/theorems/36684d67-3dc9-4323-9f07-9d9447cb21ec
-- title:
--   Proof of Theorem 4.1, p. 17 — if $p_T\le p_S$, $q_T>q_S$ and $g_S(\omega_S)>g_S(\omega_T)\ge0$, then $\bar v_T<\bar v_S$
-- statement:
--   This is the second step of the proof of Theorem 4.1.
--
--   Let $W>0$ and let $\omega_S=(p_S,q_S,\bar v_S)$ and $\omega_T=(p_T,q_T,\bar v_T)$ be two points of $\Omega=[0,1)\times[0,1)\times\mathbb R_+$, with
--   $$g_S(\omega)=\frac{\bar v-W}{1-q}-\frac{pW}{1-p}.$$
--   Suppose that
--
--   1. $p_T\le p_S$;
--   2. $q_T>q_S$;
--   3. $g_S(\omega_S)>g_S(\omega_T)$;
--   4. $g_S(\omega_T)\ge 0$.
--
--   Then
--   $$\bar v_T<\bar v_S.$$
--
--   Together with the first step, this shows that when the engagement maximizer is not more moreish, it has a longer span but a lower value.
--
--   **Formalization Note** Hypothesis 4 is the constraint of (4) satisfied by the engagement maximizer; the printed step marked "$(q_T>q_S)$" uses it silently (it gives $\bar v_T\ge W$), and the statement is false without it. $W>0$ is added: the paper fixes $W=1$ (p. 5).
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 17, proof of Theorem 4.1 (second display)

import Mathlib
import Definitions.Def_EngagementOpt_Misalign_Model

namespace EngagementOpt.Misalign

/-- Proof of Theorem 4.1, p. 17: for `ω_S, ω_T ∈ Ω` and `W > 0`, if `p_T ≤ p_S`, `q_T > q_S`,
`g_S(ω_S) > g_S(ω_T)` and `g_S(ω_T) ≥ 0` (the constraint of (4), used implicitly in the step
marked "(q_T > q_S)"), then `v̄_T < v̄_S`. -/
theorem thm_4_1_step_v (W : ℝ) (hW : 0 < W) (ωS ωT : Params) (hS : InOmega ωS)
    (hT : InOmega ωT) (hp : ωT.p ≤ ωS.p) (hq : ωS.q < ωT.q) (hgS : gS W ωT < gS W ωS)
    (hpart : 0 ≤ gS W ωT) :
    ωT.v < ωS.v := by sorry

end EngagementOpt.Misalign
