-- Prove2me | Theorems.Thm_EngagementOpt_Salad_eq_5
-- name    : EngagementOpt.Salad.eq_5
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:46.861693+00:00
-- url     : https://prove2.me/theorems/0a50bf98-051f-476b-bdc3-06e902dbd00c
-- title:
--   (5), p. 18 — g_T(ω_T) ≥ g_T(ω_S) gives b_S − b_T ≤ a_T − a_S
-- statement:
--   Let $\omega_S=(p_S,q_S,\bar v_S)$ and $\omega_T=(p_T,q_T,\bar v_T)$ be points of $\Omega$, and write $a_i=\frac{1}{1-p_i}$, $b_i=\frac{1}{1-q_i}$ for $i\in\{S,T\}$. If
--   $$\frac{1}{1-q_T}+\frac{p_T}{1-p_T}\ \ge\ \frac{1}{1-q_S}+\frac{p_S}{1-p_S},$$
--   that is $g_T(\omega_T)\ge g_T(\omega_S)$, then
--   $$b_S-b_T\ \le\ a_T-a_S .$$
--
--   In the proof of Theorem 4.2 this is applied to the engagement maximizer $\omega_T$ and the utility maximizer $\omega_S$, which is feasible for (4).
--
--   **Formalization Note** The paper prints (5) with a strict inequality, from "$\mathbb E[T(\omega_T)]>\mathbb E[T(\omega_S)]$". The definition (4) of $\omega_T$ gives only $\ge$, so (5) is posed with $\le$ under the hypothesis $g_T(\omega_T)\ge g_T(\omega_S)$; the conclusion of Theorem 4.2 (a non-strict inequality) is unaffected.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 18, proof of Theorem 4.2, eq. (5)

import Mathlib
import Definitions.Def_EngagementOpt_Salad_Model

namespace EngagementOpt.Salad

/-- (5), p. 18, posed with `≤`: if `g_T(ω_T) ≥ g_T(ω_S)` for two points of `Ω`, then
`b_S − b_T ≤ a_T − a_S`. -/
theorem eq_5 (ωS ωT : EngagementOpt.Misalign.Params) (hS : EngagementOpt.Misalign.InOmega ωS) (hT : EngagementOpt.Misalign.InOmega ωT)
    (hgT : EngagementOpt.Misalign.gT ωS ≤ EngagementOpt.Misalign.gT ωT) :
    bCoef ωS - bCoef ωT ≤ aCoef ωT - aCoef ωS := by sorry

end EngagementOpt.Salad
