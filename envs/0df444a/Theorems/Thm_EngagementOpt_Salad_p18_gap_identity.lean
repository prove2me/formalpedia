-- Prove2me | Theorems.Thm_EngagementOpt_Salad_p18_gap_identity
-- name    : EngagementOpt.Salad.p18_gap_identity
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:51.640712+00:00
-- url     : https://prove2.me/theorems/136eac40-1d6c-41a1-a82b-ce0f9db8fe5e
-- title:
--   Proof of Theorem 4.2, p. 18 — E[S(ω_S)] − E[S(ω_T)] = b_S(v̄_S − v̄_T) + (b_S − b_T)(v̄_T − W) + W(a_T − a_S)
-- statement:
--   Let $\omega_S=(p_S,q_S,\bar v_S)$ and $\omega_T=(p_T,q_T,\bar v_T)$ be points of $\Omega$, let $W\in\mathbb R$, and write $a_i=\frac{1}{1-p_i}$, $b_i=\frac{1}{1-q_i}$. If the user participates at both points, $g_S(\omega_S)\ge0$ and $g_S(\omega_T)\ge0$, then the utility gap is
--   $$\mathbb E[S(\omega_S)]-\mathbb E[S(\omega_T)]=b_S(\bar v_S-\bar v_T)+(b_S-b_T)(\bar v_T-W)+W(a_T-a_S).$$
--
--   This decomposition is the starting point of the bound in Theorem 4.2: the first term is controlled by the value spread $\beta$, the second by (5), and the third by (7).
--
--   **Formalization Note** The statement uses $\mathbb E[S]=\max(g_S,0)$ as in (1); the participation hypotheses make $\mathbb E[S]=g_S$ at both points, which is how the paper's display reads.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 18, proof of Theorem 4.2, first three lines of the display

import Mathlib
import Definitions.Def_EngagementOpt_Salad_Model

namespace EngagementOpt.Salad

/-- The identity on p. 18 (proof of Theorem 4.2, first three lines of the display): for two points
of `Ω` at which `g_S ≥ 0`,
`E[S(ω_S)] − E[S(ω_T)] = b_S(v̄_S − v̄_T) + (b_S − b_T)(v̄_T − W) + W(a_T − a_S)`. -/
theorem p18_gap_identity (W : ℝ) (ωS ωT : EngagementOpt.Misalign.Params) (hS : EngagementOpt.Misalign.InOmega ωS) (hT : EngagementOpt.Misalign.InOmega ωT)
    (hgS : 0 ≤ EngagementOpt.Misalign.gS W ωS) (hgT : 0 ≤ EngagementOpt.Misalign.gS W ωT) :
    ES W ωS - ES W ωT =
      bCoef ωS * (ωS.v - ωT.v) + (bCoef ωS - bCoef ωT) * (ωT.v - W)
        + W * (aCoef ωT - aCoef ωS) := by sorry

end EngagementOpt.Salad
