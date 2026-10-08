-- Prove2me | Theorems.Thm_DaiYuanCG_Conv_eq_3_6
-- name    : DaiYuanCG.Conv.eq_3_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:22.648579+00:00
-- url     : https://prove2.me/theorems/49253fb5-d32f-4fcb-ac00-526b24d0d121
-- title:
--   (3.6), p. 179 (continued on p. 180) — f_k − f_{k+1} ≥ c (g_kᵀd_k)²/‖d_k‖² with c = δ(1 − σ)/L
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ and let $0<\delta<\sigma<1$. Suppose Assumption 3.1 holds at $x_1$ with neighbourhood $\mathcal N$ and Lipschitz constant $L>0$: $f$ is bounded below, $\mathcal N$ is an open set containing the level set $\{x: f(x)\le f(x_1)\}$, $f$ is continuously differentiable in $\mathcal N$, and $\|\nabla f(x)-\nabla f(y)\|\le L\|x-y\|$ for $x,y\in\mathcal N$. Consider any method $x_{k+1}=x_k+\alpha_kd_k$ ($k\ge1$) with $\alpha_k>0$, descent directions $g_k^Td_k<0$, and steps satisfying the standard Wolfe conditions (1.7) and (1.10). Then for every $k\ge1$
--   $$f_k-f_{k+1}\ge c\,\frac{(g_k^Td_k)^2}{\|d_k\|^2},\qquad c=\frac{\delta(1-\sigma)}{L}.$$
--
--   Summed over $k$, this gives the Zoutendijk condition (Lemma 3.2).
--
--   **Formalization Note** The iterates stay in the level set (by (1.7) and descent) and hence in $\mathcal N$, where the Lipschitz bound applies; this is a consequence, not a hypothesis. The quotient is a Lean division whose denominator is nonzero because $g_k^Td_k<0$ forces $d_k\neq0$.
-- source:
--   Dai and Yuan, A nonlinear conjugate gradient method with a strong global convergence property, SIAM J. Optim. 10 (1999), pp. 179–180, (3.3)–(3.6), proof of Lemma 3.2

import Mathlib
import Definitions.Def_DaiYuanCG_Conv_Setting

namespace DaiYuanCG.Conv

theorem eq_3_6 {n : ℕ} (f : E n → ℝ) (N : Set (E n)) (L : ℝ)
    (δ σ : ℝ) (hδ : 0 < δ) (hδσ : δ < σ) (hσ1 : σ < 1)
    (x d : ℕ → E n) (α : ℕ → ℝ) (hA : Assumption31 f (x 1) N L)
    (hm : IsDescentWolfeMethod f δ σ x d α) :
    ∀ k, 1 ≤ k → δ * (1 - σ) / L * (inner ℝ (gradient f (x k)) (d k) ^ 2 / ‖d k‖ ^ 2) ≤
      f (x k) - f (x (k + 1)) := by sorry

end DaiYuanCG.Conv
