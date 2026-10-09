-- Prove2me | Theorems.Thm_DynAssortPers_Regret_lemma_revenue_lipschitz
-- name    : DynAssortPers.Regret.lemma_revenue_lipschitz
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:15:40.822297+00:00
-- url     : https://prove2.me/theorems/7844581d-e890-4d48-8b53-e20acb8bab73
-- title:
--   p. 47 — $|F(S;w,\theta)-F(S;w,\theta')|\le\frac14\|w\|_\infty K^{3/2}\|\theta-\theta'\|_2$ for $|S|\le K$
-- statement:
--   Let $S$ be an assortment with $|S|\le K$, $w\in\mathbb R^n$ a revenue vector and $\theta,\theta'\in\mathbb R^n$. The MNL expected revenue $F(S;w,\theta)=\sum_{j\in S}p_j(S;\theta)w_j$ satisfies
--   $$|F(S;w,\theta)-F(S;w,\theta')|\le\frac14\,\|w\|_\infty\,K^{3/2}\,\|\theta-\theta'\|_2 .$$
--
--   It bounds the revenue lost by evaluating an assortment under estimated rather than true parameters.
--
--   **Formalization Note** $K^{3/2}$ is the real power `(K:ℝ) ^ ((3:ℝ)/2)`; $\|w\|_\infty=\max_j|w_j|$. The page states the chain $|F(S;w,\theta)-F(S;w,\theta')|\le\sum_{j\in S}|w_j||p_j(S;\theta)-p_j(S;\theta')|\le\frac14\|w\|_\infty K^{3/2}\|\theta-\theta'\|_2$; the outer inequality is formalized.
-- source:
--   Kallus, Udell, Dynamic Assortment Personalization in High Dimensions, arXiv:1610.05604 (PDF sha256 2b010481…216a), proof of Theorem 6, p. 47, display after 'the expected revenue loss associated with choosing set S′ instead of S is bounded by'

import Mathlib
import Definitions.Def_DynAssortPers_Regret_MNL

namespace DynAssortPers.Regret

/-- Proof of Theorem 6, p. 47: for any `S` with `|S| ≤ K`, `w`, `θ`, `θ'`,
`|F(S; w, θ) − F(S; w, θ')| ≤ (1/4) ‖w‖_∞ K^{3/2} ‖θ − θ'‖₂`. -/
theorem lemma_revenue_lipschitz {n : ℕ} (K : ℕ) (S : Finset (Fin n)) (hS : S.card ≤ K)
    (w θ θ' : Fin n → ℝ) :
    |revenue S w θ - revenue S w θ'| ≤
      (1 / 4) * supNorm w * (K : ℝ) ^ ((3 : ℝ) / 2) * euclidDist θ θ' := by sorry

end DynAssortPers.Regret
