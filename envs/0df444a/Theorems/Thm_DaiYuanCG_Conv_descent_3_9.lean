-- Prove2me | Theorems.Thm_DaiYuanCG_Conv_descent_3_9
-- name    : DaiYuanCG.Conv.descent_3_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:00:48.553285+00:00
-- url     : https://prove2.me/theorems/320d4ca0-857e-4487-88f0-1ba22db2fc11
-- title:
--   (3.9)–(3.10), p. 180 — along a non-terminating run of Algorithm 2.1, g_kᵀd_k < 0 and d_kᵀy_k ≥ (σ − 1)d_kᵀg_k > 0
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, $\sigma<1$, and let $(x_k,d_k,\alpha_k)_{k\ge1}$ be a run of Algorithm 2.1 (the Dai–Yuan iteration $d_1=-g_1$, $x_{k+1}=x_k+\alpha_kd_k$, $d_{k+1}=-g_{k+1}+\beta_kd_k$, $\beta_k=\|g_{k+1}\|^2/d_k^Ty_k$, with every $\alpha_k>0$ satisfying the standard Wolfe conditions (1.7) and (1.10) with constants $\delta,\sigma$). Suppose the algorithm does not terminate, i.e. $g_k\neq0$ for all $k\ge1$. Then for every $k\ge1$
--   $$g_k^Td_k<0\qquad\text{and}\qquad d_k^Ty_k\ge(\sigma-1)\,d_k^Tg_k>0 .$$
--
--   All search directions are therefore descent directions, and the denominator of $\beta_k$ is positive, so $\beta_k>0$ is well defined at every iteration. This is the first step of the proof of Theorem 3.3.
--
--   **Formalization Note** Neither Assumption 3.1 nor the bound $\delta>0$ is used by this step, so they are dropped; only $\sigma<1$ and the run are assumed. Non-termination is the hypothesis $g_k\neq0$ for all $k\ge1$, which is (3.8).
-- source:
--   Dai and Yuan, A nonlinear conjugate gradient method with a strong global convergence property, SIAM J. Optim. 10 (1999), p. 180, (3.9)–(3.10), proof of Theorem 3.3

import Mathlib
import Definitions.Def_DaiYuanCG_Conv_Setting

namespace DaiYuanCG.Conv

theorem descent_3_9 {n : ℕ} (f : E n → ℝ) (δ σ : ℝ) (hσ1 : σ < 1)
    (x d : ℕ → E n) (α : ℕ → ℝ) (hrun : IsDYRun f δ σ x d α)
    (hnt : ∀ k, 1 ≤ k → gradient f (x k) ≠ 0) :
    ∀ k, 1 ≤ k → inner ℝ (gradient f (x k)) (d k) < 0 ∧
      (σ - 1) * inner ℝ (d k) (gradient f (x k)) ≤
        inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) ∧
      0 < inner ℝ (d k) (gradient f (x (k + 1)) - gradient f (x k)) := by sorry

end DaiYuanCG.Conv
