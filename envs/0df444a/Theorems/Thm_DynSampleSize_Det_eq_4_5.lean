-- Prove2me | Theorems.Thm_DynSampleSize_Det_eq_4_5
-- name    : DynSampleSize.Det.eq_4_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:48.541229+00:00
-- url     : https://prove2.me/theorems/ecfae2e4-c9fe-4db6-a231-b004e5fb37ad
-- title:
--   (4.5) — the squared gradient bounds the optimality gap: $\nabla J(w)^T\nabla J(w) \ge \lambda[J(w)-J(w_*)]$
-- statement:
--   Let $J : \mathbb{R}^m \to \mathbb{R}$ be twice continuously differentiable with Hessian bounds $\lambda\|d\|^2 \le d^T\nabla^2J(w)d \le L\|d\|^2$ for all $w, d$, where $0<\lambda<L$ (assumption (4.2)), and let $w_*$ be a minimizer of $J$. Then for every $w \in \mathbb{R}^m$,
--
--   $$
--   \nabla J(w)^T \nabla J(w) \;\ge\; \lambda\,[J(w) - J(w_*)].
--   $$
--
--   This is a gradient-dominance (Polyak–Łojasiewicz type) inequality with constant $\lambda$. It turns a per-step decrease proportional to $\|\nabla J(w_k)\|^2$ into a linear contraction of the optimality gap.
--
--   **Formalization Note** The paper states (4.5) at an iterate $w_k$; the Lean statement holds for an arbitrary point $w$. The minimizer is given as a point $w_*$ with $J(w_*) \le J(w)$ for all $w$; the convenience assumption $J(w_*)=0$ is not used here.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 8, (4.5)

import Mathlib
import Definitions.Def_DynSampleSize_Det_Setting

open Filter Topology

namespace DynSampleSize.Det

theorem eq_4_5 {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hmin : ∀ w, J wstar ≤ J w) (w : EuclideanSpace ℝ (Fin m)) :
    lam * (J w - J wstar) ≤ inner ℝ (gradient J w) (gradient J w) := by sorry

end DynSampleSize.Det
