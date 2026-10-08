-- Prove2me | Theorems.Thm_DaiYuanCG_Conv_eq_2_5
-- name    : DaiYuanCG.Conv.eq_2_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:00:59.914847+00:00
-- url     : https://prove2.me/theorems/4d004726-8c0c-40c1-bb6d-188850e87953
-- title:
--   (2.5), p. 179 — g_{k+1}ᵀd_{k+1} = (‖g_{k+1}‖²/d_kᵀy_k) g_kᵀd_k = β_k g_kᵀd_k
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, write $g_k=\nabla f(x_k)$ and $y_k=g_{k+1}-g_k$, and let $(x_k,d_k,\alpha_k)_{k\ge1}$ follow the Dai–Yuan iteration: $d_1=-g_1$, $\alpha_k>0$, $x_{k+1}=x_k+\alpha_kd_k$ and $d_{k+1}=-g_{k+1}+\beta_kd_k$ with $\beta_k=\|g_{k+1}\|^2/d_k^Ty_k$. Then for every $k\ge1$ with $d_k^Ty_k\neq0$,
--   $$g_{k+1}^Td_{k+1}=\frac{\|g_{k+1}\|^2}{d_k^Ty_k}\,g_k^Td_k=\beta_k\,g_k^Td_k .$$
--
--   Equivalently, $\beta_k=g_{k+1}^Td_{k+1}/g_k^Td_k$ (the paper's (2.6)). This identity is the engine of the whole convergence analysis: it transfers the sign of $g_k^Td_k$ to $g_{k+1}^Td_{k+1}$ and drives the recurrence (3.13).
--
--   **Formalization Note** The hypothesis $d_k^Ty_k\neq0$ is added: the paper has $d_k^Ty_k>0$ at this point from the line-search condition (1.10) ("This formula is well defined because …"), and without it the identity fails (Lean's $\beta_k$ is then $0$). No line-search condition is assumed here.
-- source:
--   Dai and Yuan, A nonlinear conjugate gradient method with a strong global convergence property, SIAM J. Optim. 10 (1999), p. 179, (2.5) (and its rewriting (2.6))

import Mathlib
import Definitions.Def_DaiYuanCG_Conv_Setting

namespace DaiYuanCG.Conv

theorem eq_2_5 {n : ℕ} (f : E n → ℝ) (x d : ℕ → E n) (α : ℕ → ℝ)
    (hit : IsDYIteration f x d α) (k : ℕ) (hk : 1 ≤ k)
    (hy : inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) ≠ 0) :
    inner ℝ (gradient f (x (k + 1))) (d (k + 1)) =
        ‖gradient f (x (k + 1))‖ ^ 2 /
          inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) *
          inner ℝ (gradient f (x k)) (d k) ∧
      inner ℝ (gradient f (x (k + 1))) (d (k + 1)) =
        betaDY f x d k * inner ℝ (gradient f (x k)) (d k) := by sorry

end DaiYuanCG.Conv
