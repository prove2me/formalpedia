-- Prove2me | Theorems.Thm_DaiYuanCG_Conv_eq_3_14
-- name    : DaiYuanCG.Conv.eq_3_14
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:00:58.802987+00:00
-- url     : https://prove2.me/theorems/10b7f8ab-fced-4d94-80d6-b37d590050cf
-- title:
--   (3.14), p. 180 — ‖d_k‖²/(g_kᵀd_k)² ≤ Σ_{i=1}^k 1/‖g_i‖²
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, $\sigma<1$, and let $(x_k,d_k,\alpha_k)_{k\ge1}$ be a non-terminating run of Algorithm 2.1 (standard Wolfe steps with constants $\delta,\sigma$, and $g_k\neq0$ for every $k\ge1$). Then for every $k\ge1$
--   $$\frac{\|d_k\|^2}{(g_k^Td_k)^2}\le\sum_{i=1}^{k}\frac{1}{\|g_i\|^2}.$$
--
--   It follows from the recurrence (3.13) together with $\|d_1\|^2/(g_1^Td_1)^2=1/\|g_1\|^2$. With gradients bounded away from zero, it bounds the reciprocal Zoutendijk terms linearly in $k$.
--
--   **Formalization Note** Assumption 3.1 and $\delta>0$ are not used and are dropped. The quotients are Lean divisions with nonzero denominators along the run.
-- source:
--   Dai and Yuan, A nonlinear conjugate gradient method with a strong global convergence property, SIAM J. Optim. 10 (1999), p. 180, (3.14), proof of Theorem 3.3

import Mathlib
import Definitions.Def_DaiYuanCG_Conv_Setting

namespace DaiYuanCG.Conv

theorem eq_3_14 {n : ℕ} (f : E n → ℝ) (δ σ : ℝ) (hσ1 : σ < 1)
    (x d : ℕ → E n) (α : ℕ → ℝ) (hrun : IsDYRun f δ σ x d α)
    (hnt : ∀ k, 1 ≤ k → gradient f (x k) ≠ 0) :
    ∀ k, 1 ≤ k → ‖d k‖ ^ 2 / inner ℝ (gradient f (x k)) (d k) ^ 2 ≤
      ∑ i ∈ Finset.Icc 1 k, 1 / ‖gradient f (x i)‖ ^ 2 := by sorry

end DaiYuanCG.Conv
