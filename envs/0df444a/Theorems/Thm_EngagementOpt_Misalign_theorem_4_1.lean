-- Prove2me | Theorems.Thm_EngagementOpt_Misalign_theorem_4_1
-- name    : EngagementOpt.Misalign.theorem_4_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-16T08:05:52.299479+00:00
-- url     : https://prove2.me/theorems/7a66f147-6bfd-45a5-9068-7a01aaa7a290
-- title:
--   Theorem 4.1 — engagement beats utility only through higher moreishness, or higher span with lower value
-- statement:
--   Let $W>0$ be the user's per-step outside option and let $\mathcal M\subseteq\Omega=[0,1)\times[0,1)\times\mathbb R_+$ be a content manifold of content distributions $\omega=(p,q,\bar v)$ (moreishness, span, value). Assume, as the paper does, that $\mathcal M$ contains at least one point with $g_S(\omega)>0$, where
--   $$g_S(\omega)=\frac{\bar v-W}{1-q}-\frac{pW}{1-p},\qquad g_T(\omega)=\frac1{1-q}+\frac{p}{1-p}.$$
--   Let $\omega_S=(p_S,q_S,\bar v_S)$ maximize $g_S$ over $\mathcal M$ (3), and let $\omega_T=(p_T,q_T,\bar v_T)$ maximize $g_T$ over $\{\omega\in\mathcal M: g_S(\omega)\ge0\}$, with $g_S(\omega_T)\ge0$ (4).
--
--   Suppose $\omega_S\ne\omega_T$ and that the disagreement is strict:
--   $$g_S(\omega_S)>g_S(\omega_T)\qquad\text{and}\qquad g_T(\omega_T)>g_T(\omega_S).$$
--   Then at least one of the following holds:
--
--   1. $p_T>p_S$ ($\omega_T$ has higher moreishness);
--   2. $q_T>q_S$ and $\bar v_T<\bar v_S$ ($\omega_T$ has higher span but lower value).
--
--   The theorem names the only two ways in which a platform that maximizes engagement (expected session length) can end up serving content that is worse for the user's forward-looking self: the content is more habit-forming, or it holds the user longer while delivering less value per item.
--
--   **Formalization Note** $W>0$ is added (the paper fixes $W=1$ without loss of generality, p. 5). The maximizers are taken as hypotheses (any points attaining the maxima of (3) and (4)), so the paper's tie-breaking rule and its closedness assumption on $\mathcal M$, which only serve to make the $\arg\max$ well defined, are not needed. The standing assumption that $\mathcal M$ has a point with $g_S>0$ (p. 16) is kept as printed. "One of the following" is an inclusive or.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 16, Theorem 4.1 (with (3), (4) and the standing assumption on the same page; Ω on p. 15)

import Mathlib
import Definitions.Def_EngagementOpt_Misalign_Model

namespace EngagementOpt.Misalign

/-- Theorem 4.1, p. 16. Let `M ⊆ Ω` be a content manifold containing a point with `g_S > 0`
(p. 16), let `W > 0`, and let `ω_S`, `ω_T` be maximizers (3), (4). If `ω_S ≠ ω_T` and the
disagreement is strict, `g_S(ω_S) > g_S(ω_T)` and `g_T(ω_T) > g_T(ω_S)`, then
`p_T > p_S`, or `q_T > q_S` and `v̄_T < v̄_S`. -/
theorem theorem_4_1 (W : ℝ) (hW : 0 < W) (M : Set Params) (hM : ∀ ω ∈ M, InOmega ω)
    (hpos : ∃ ω ∈ M, 0 < gS W ω) (ωS ωT : Params)
    (hS : IsUtilityMaximizer W M ωS) (hT : IsEngagementMaximizer W M ωT)
    (hne : ωS ≠ ωT) (hdisS : gS W ωT < gS W ωS) (hdisT : gT ωS < gT ωT) :
    ωS.p < ωT.p ∨ (ωS.q < ωT.q ∧ ωT.v < ωS.v) := by sorry

end EngagementOpt.Misalign
