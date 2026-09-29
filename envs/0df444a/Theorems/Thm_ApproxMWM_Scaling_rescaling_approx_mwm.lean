-- Prove2me | Theorems.Thm_ApproxMWM_Scaling_rescaling_approx_mwm
-- name    : ApproxMWM.Scaling.rescaling_approx_mwm
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-09-27T13:08:08.163658+00:00
-- url     : https://prove2.me/theorems/e21f2a94-6822-4f9f-b8a7-b701bec6ca36
-- title:
--   Section 2 — rounding weights to integers loses at most a factor $1-\epsilon/2$
-- statement:
--   Let $G=(V,E)$ be a finite simple graph with $n=|V|$ vertices and nonnegative edge weights $w$, let $w_{\max}=\max_{e\in E}w(e)>0$, and let $0<\epsilon<1$. Put $\gamma_r=\epsilon\,w_{\max}/n$ and define the rounded weights $\tilde w(e)=\lfloor w(e)/\gamma_r\rfloor$. If $M$ is a $(1-\epsilon/2)$-MWM with respect to $\tilde w$, then for every matching $M'$ of $G$
--   $$w(M)\ >\ (1-\epsilon)\,w(M').$$
--   In particular $M$ is a $(1-\epsilon)$-MWM with respect to $w$.
--
--   This justifies the standing assumption of the paper that edge weights are integers in $\{1,\dots,N\}$ with $N$ polynomial in $n$.
--
--   **Formalization Note** The page writes this argument as an unnumbered chain of inequalities for a maximum weight matching $M^*$; here the strict conclusion is stated for every matching $M'$, which follows since $w(M')\le w(M^*)$ and $1-\epsilon>0$. The page's $\gamma=\epsilon w_{\max}/n$ is unrelated to $\gamma=\log\epsilon'^{-1}$ of Definition 3.10. $w_{\max}$ is given by the hypotheses that it bounds every edge weight and is attained.
-- source:
--   Duan and Pettie, Linear-Time Approximation for Maximum Weight Matching, J. ACM 61(1), Article 1 (2014), https://doi.org/10.1145/2529989, pp. 1:8–1:9, Section 2, display on pp. 1:8–1:9

import Mathlib
import Definitions.Def_ApproxMWM_Scaling_Matching

namespace ApproxMWM.Scaling

/-- Section 2, display on pp. 1:8–1:9 (Duan–Pettie, J. ACM 61(1) 2014): rounding the weights.
Let `G` have `n = |V|` vertices and nonnegative edge weights `w` with maximum
`w_max = max_e w(e) > 0`, and let `0 < ε < 1`. Put `γ_r = ε · w_max / n` and
`w̃(e) = ⌊w(e) / γ_r⌋`. If `M` is a `(1 - ε/2)`-MWM with respect to `w̃`, then
`w(M) > (1 - ε) · w(M')` for every matching `M'` of `G`; in particular `M` is a `(1 - ε)`-MWM
with respect to `w`. -/
theorem rescaling_approx_mwm {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (w : Sym2 V → ℝ) (ε wmax : ℝ) (hε : 0 < ε) (hε1 : ε < 1)
    (hw_nonneg : ∀ e ∈ G.edgeSet, 0 ≤ w e)
    (hwmax_ge : ∀ e ∈ G.edgeSet, w e ≤ wmax)
    (hwmax_att : ∃ e ∈ G.edgeSet, w e = wmax)
    (hwmax_pos : 0 < wmax)
    (M : Finset (Sym2 V))
    (hM : IsApproxMWM G (fun e => ((⌊w e / (ε * wmax / (Fintype.card V : ℝ))⌋ : ℤ) : ℝ))
      (1 - ε / 2) M) :
    IsMatching G M ∧ ∀ M' : Finset (Sym2 V), IsMatching G M' → (1 - ε) * weight w M' < weight w M := by sorry

end ApproxMWM.Scaling
