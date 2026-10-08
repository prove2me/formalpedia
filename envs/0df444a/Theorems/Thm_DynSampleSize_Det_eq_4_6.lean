-- Prove2me | Theorems.Thm_DynSampleSize_Det_eq_4_6
-- name    : DynSampleSize.Det.eq_4_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:28.632974+00:00
-- url     : https://prove2.me/theorems/52496d5a-bed0-4180-aea4-3323a39cd905
-- title:
--   (4.6) — the optimality gap bounds the squared gradient: $J(w)-J(w_*) \ge \frac{\lambda}{2L^2}\|\nabla J(w)\|_2^2$
-- statement:
--   Let $J : \mathbb{R}^m \to \mathbb{R}$ be twice continuously differentiable with Hessian bounds $\lambda\|d\|^2 \le d^T\nabla^2J(w)d \le L\|d\|^2$ for all $w, d$, where $0<\lambda<L$ (assumption (4.2)), and let $w_*$ be a minimizer of $J$. Then for every $w \in \mathbb{R}^m$,
--
--   $$
--   J(w) - J(w_*) \;\ge\; \frac{\lambda}{2L^2}\,\|\nabla J(w)\|_2^2 .
--   $$
--
--   Together with (4.5) this shows that $J(w)-J(w_*)$ and $\|\nabla J(w)\|^2$ are equivalent up to constants depending on $\lambda$ and $L$. In Theorem 4.1 it converts the linear decay of $J(w_k)$ into the bound (4.12) on the approximate gradients.
--
--   **Formalization Note** Stated for an arbitrary point $w$ rather than an iterate $w_k$. The minimizer is a point $w_*$ with $J(w_*) \le J(w)$ for all $w$.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 8, (4.6)

import Mathlib
import Definitions.Def_DynSampleSize_Det_Setting

open Filter Topology

namespace DynSampleSize.Det

theorem eq_4_6 {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hmin : ∀ w, J wstar ≤ J w) (w : EuclideanSpace ℝ (Fin m)) :
    lam / (2 * L ^ 2) * ‖gradient J w‖ ^ 2 ≤ J w - J wstar := by sorry

end DynSampleSize.Det
