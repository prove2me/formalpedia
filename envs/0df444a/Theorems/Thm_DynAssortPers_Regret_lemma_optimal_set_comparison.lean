-- Prove2me | Theorems.Thm_DynAssortPers_Regret_lemma_optimal_set_comparison
-- name    : DynAssortPers.Regret.lemma_optimal_set_comparison
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:15:53.42279+00:00
-- url     : https://prove2.me/theorems/610b1fa3-34cf-46ec-a2ce-d3b2560d45ab
-- title:
--   p. 47 — $F(S';w,\theta)\ge F(S;w,\theta)-\frac12\|w\|_\infty K^{3/2}\|\theta-\theta'\|_2$ for $S\in S^\star(w,\theta;K)$, $S'\in S^\star(w,\theta';K)$
-- statement:
--   Let $w,\theta,\theta'\in\mathbb R^n$, let $S\in S^\star(w,\theta;K)$ be optimal under $\theta$ and $S'\in S^\star(w,\theta';K)$ optimal under $\theta'$. Then the assortment optimal for $\theta'$ is nearly optimal for $\theta$:
--   $$F(S';w,\theta)\ge F(S;w,\theta)-\frac12\,\|w\|_\infty\,K^{3/2}\,\|\theta-\theta'\|_2 .$$
--
--   This is the revenue cost of exploiting an estimate $\theta'$ in place of the true parameter $\theta$.
--
--   **Formalization Note** The page displays a three-line chain; its end-to-end inequality is formalized. $S^\star(w,\theta;K)$ is the set of maximizers of $F(\cdot;w,\theta)$ over assortments of size at most $K$.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), proof of Theorem 6, p. 47, display after 'Therefore, letting S ∈ S⋆(w, θ; K) and S′ ∈ S⋆(w, θ′; K)'

import Mathlib
import Definitions.Def_DynAssortPers_Regret_MNL

namespace DynAssortPers.Regret

/-- Proof of Theorem 6, p. 47: for `S ∈ S⋆(w, θ; K)` and `S' ∈ S⋆(w, θ'; K)`,
`F(S'; w, θ) ≥ F(S; w, θ) − (1/2) ‖w‖_∞ K^{3/2} ‖θ − θ'‖₂`. -/
theorem lemma_optimal_set_comparison {n : ℕ} (K : ℕ) (w θ θ' : Fin n → ℝ)
    (S S' : Finset (Fin n)) (hS : IsOptimal w θ K S) (hS' : IsOptimal w θ' K S') :
    revenue S w θ - (1 / 2) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ' ≤
      revenue S' w θ := by sorry

end DynAssortPers.Regret
