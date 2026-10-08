-- Prove2me | Theorems.Thm_DynSampleSize_Stoch_eq_4_5
-- name    : DynSampleSize.Stoch.eq_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:17.417977+00:00
-- url     : https://prove2.me/theorems/a2714968-a288-4f79-8d24-58613e4050e1
-- title:
--   (4.5) — the squared gradient bounds the optimality gap, $\nabla J^T\nabla J \ge \lambda[J(w)-J(w^*)]$
-- statement:
--   Let $J:\mathbb R^m\to\mathbb R$ be twice continuously differentiable and uniformly convex with constants $0<\lambda<L$, i.e. $\lambda\|d\|^2\le d^T\nabla^2J(w)d\le L\|d\|^2$ for all $w,d$ (4.2), and let $w^*$ minimize $J$. Then for every $w\in\mathbb R^m$,
--
--   $$
--   \nabla J(w)^T\nabla J(w)\;\ge\;\lambda\,[J(w)-J(w^*)].
--   $$
--
--   This gradient-dominance inequality converts a decrease proportional to $\|\nabla J\|^2$ into a contraction of the optimality gap; it is the step from (4.26) to (4.27).
--
--   **Formalization Note** The paper states the inequality at the iterate $w_k$, which is an arbitrary point there; it is stated for every $w$. The constant is the paper's $\lambda$ (named `lam`), not the sharper $2\lambda$.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 8, (4.5)

import Mathlib
import Definitions.Def_DynSampleSize_Stoch_UniformConvexity

namespace DynSampleSize.Stoch

/-- (4.5), p. 8: under (4.2), with `wstar` a minimizer of `J`, for every `w`,
`∇J(w)ᵀ∇J(w) ≥ λ [J(w) − J(w*)]`. -/
theorem eq_4_5 {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : UniformlyConvex J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hwstar : ∀ w, J wstar ≤ J w) (w : EuclideanSpace ℝ (Fin m)) :
    lam * (J w - J wstar) ≤ inner ℝ (gradient J w) (gradient J w) := by sorry

end DynSampleSize.Stoch
