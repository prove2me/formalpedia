-- Prove2me | Theorems.Thm_DynAssortPers_Regret_lemma_optimal_set_stable
-- name    : DynAssortPers.Regret.lemma_optimal_set_stable
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:15:49.709988+00:00
-- url     : https://prove2.me/theorems/e60fec00-57cc-43f5-b489-fac0e98d3e2a
-- title:
--   p. 47 (corrected) — if $\delta(w,\theta;K)\ge d\ge\frac12\|w\|_\infty K^{3/2}\|\theta-\theta'\|_2$ then $S^\star(w,\theta';K)\subseteq S^\star(w,\theta;K)$
-- statement:
--   Let $w,\theta,\theta'\in\mathbb R^n$ and $d\in\mathbb R$. Suppose the revenue gap under $\theta$ is at least $d$: every assortment $S$ with $|S|\le K$ that is not optimal under $\theta$ satisfies $F(S;w,\theta)\le\max_{|S'|\le K}F(S';w,\theta)-d$. If
--   $$\frac12\,\|w\|_\infty\,K^{3/2}\,\|\theta-\theta'\|_2\le d,$$
--   then every assortment optimal under $\theta'$ is optimal under $\theta$:
--   $$S^\star(w,\theta';K)\subseteq S^\star(w,\theta;K).$$
--
--   In the proof of Theorem 6 this is what makes an exploitation round optimal once the estimate is close enough to the true parameters.
--
--   **Formalization Note** The page prints the conclusion as the equality $S^\star(w,\theta';K)=S^\star(w,\theta;K)$ under $\|\theta-\theta'\|_2\le2\delta(w,\theta;K)K^{-3/2}/\|w\|_\infty$. That is false: for $n=2$, $K=1$, $w=(1,1)$, $\theta=(0,0)$, $\theta'=(\varepsilon,0)$, both singletons are optimal under $\theta$ but only $\{1\}$ under $\theta'$, while $\delta(w,\theta;1)=\frac12$ (only $\emptyset$ is suboptimal) and $\varepsilon\le1$. The statement here keeps the page's non-strict hypothesis and replaces the equality by the inclusion; the hypothesis is multiplied out so that $\|w\|_\infty=0$ needs no division.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), proof of Theorem 6, p. 47, display after 'It follows that if ||θ − θ′||_2 is small enough, the optimal assortment for each is the same' (corrected)

import Mathlib
import Definitions.Def_DynAssortPers_Regret_MNL

namespace DynAssortPers.Regret

/-- Proof of Theorem 6, p. 47, the stability of the optimal set, in its corrected form: if every
non-optimal feasible assortment under `θ` earns at most the optimum minus `d` (that is,
`δ(w, θ; K) ≥ d`) and `(1/2) ‖w‖_∞ K^{3/2} ‖θ − θ'‖₂ ≤ d` (the page's `‖θ − θ'‖₂ ≤ 2δ(w, θ; K)K^{−3/2}/‖w‖_∞`,
multiplied out), then `S⋆(w, θ'; K) ⊆ S⋆(w, θ; K)`. (The printed equality of the two sets is false.) -/
theorem lemma_optimal_set_stable {n : ℕ} (K : ℕ) (w θ θ' : Fin n → ℝ) (d : ℝ)
    (hgap : HasGap w θ K d)
    (hclose : (1 / 2) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ' ≤ d)
    (S : Finset (Fin n)) (hS : IsOptimal w θ' K S) :
    IsOptimal w θ K S := by sorry

end DynAssortPers.Regret
