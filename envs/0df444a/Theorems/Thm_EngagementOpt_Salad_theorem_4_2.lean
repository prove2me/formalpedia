-- Prove2me | Theorems.Thm_EngagementOpt_Salad_theorem_4_2
-- name    : EngagementOpt.Salad.theorem_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T09:42:52.984013+00:00
-- url     : https://prove2.me/theorems/41706567-34d9-43ac-98f9-763365537db4
-- title:
--   Theorem 4.2, p. 17 — on a low-moreishness, near-constant-value manifold, E[S(ω_T)] ≥ E[S(ω_S)] − 2βE[T(ω_S)] − α(v₀ + β)/(1 − α)
-- statement:
--   Let $W>0$ be the outside option and let $\mathcal M\subseteq\Omega=[0,1)\times[0,1)\times\mathbb R_+$ be a content manifold containing at least one point with strictly positive expected utility, $g_S(\omega)>0$. Let $\omega_S=(p_S,q_S,\bar v_S)$ be a maximizer of $g_S$ over $\mathcal M$ (3), and let $\omega_T=(p_T,q_T,\bar v_T)$ be a maximizer of $g_T$ over $\{\omega\in\mathcal M: g_S(\omega)\ge0\}$ with $g_S(\omega_T)\ge0$ (4). Suppose that
--
--   1. $p\le\alpha$ for all $(p,q,\bar v)\in\mathcal M$, where $\alpha<1$;
--   2. for some $v_0$, $|\bar v-v_0|<\beta$ for all $(p,q,\bar v)\in\mathcal M$.
--
--   Then the user's utility at $\omega_T$ is not much less than its utility at $\omega_S$:
--   $$\mathbb E[S(\omega_T)]\ \ge\ \mathbb E[S(\omega_S)]-2\beta\,\mathbb E[T(\omega_S)]-\frac{\alpha(v_0+\beta)}{1-\alpha}.$$
--
--   Here $\mathbb E[S(\omega)]=\max(g_S(\omega),0)$ is system 2's expected utility (1), and $\mathbb E[T(\omega)]$ is the expected session length (2), which is $0$ when $g_S(\omega)<0$. When $\alpha$ and $\beta$ are close to $0$, maximizing engagement is near-optimal for the user.
--
--   **Formalization Note** Three hypotheses implicit in the paper are explicit: $W>0$ (§2.1 normalizes $W=1$), $\alpha<1$ (without it condition 1 is vacuous on $\Omega$ and the bound fails), and the paper's standing assumption (p. 16) that $\mathcal M$ contains a point with $\mathbb E[S]>0$. "For some $v_0$" is expressed by taking $v_0$ as a parameter satisfying condition 2, which is equivalent because $v_0$ appears in the conclusion. The theorem holds for every pair of maximizers, so no tie-breaking rule and no closedness of $\mathcal M$ are needed.
-- source:
--   Kleinberg, Mullainathan, Raghavan, The Challenge of Understanding What Users Want, arXiv:2202.11776v3, p. 17, Theorem 4.2 (with (1), (2) pp. 7–8 and (3), (4) p. 16)

import Mathlib
import Definitions.Def_EngagementOpt_Salad_Model

namespace EngagementOpt.Salad

/-- Theorem 4.2, p. 17. Let `M ⊆ Ω` be a content manifold containing a point with `g_S > 0`, let
`ω_S` maximize `g_S` over `M` (3) and `ω_T` maximize `g_T` over `{ω ∈ M : g_S(ω) ≥ 0}` (4).
If `p ≤ α < 1` and `|v̄ − v₀| < β` on all of `M`, then
`E[S(ω_T)] ≥ E[S(ω_S)] − 2βE[T(ω_S)] − α(v₀ + β)/(1 − α)`. -/
theorem theorem_4_2 (W : ℝ) (hW : 0 < W) (M : Set EngagementOpt.Misalign.Params) (hM : ∀ ω ∈ M, EngagementOpt.Misalign.InOmega ω)
    (hpos : ∃ ω ∈ M, 0 < EngagementOpt.Misalign.gS W ω)
    (ωS ωT : EngagementOpt.Misalign.Params) (hωS : EngagementOpt.Misalign.IsUtilityMaximizer W M ωS) (hωT : EngagementOpt.Misalign.IsEngagementMaximizer W M ωT)
    (α : ℝ) (hα : α < 1) (h1 : ∀ ω ∈ M, ω.p ≤ α)
    (v0 β : ℝ) (h2 : ∀ ω ∈ M, |ω.v - v0| < β) :
    ES W ωT ≥ ES W ωS - 2 * β * ET W ωS - α * (v0 + β) / (1 - α) := by sorry

end EngagementOpt.Salad
