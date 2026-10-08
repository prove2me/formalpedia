-- Prove2me | Theorems.Thm_DaiYuanCG_Conv_eq_3_13
-- name    : DaiYuanCG.Conv.eq_3_13
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:00:55.952989+00:00
-- url     : https://prove2.me/theorems/716c6624-f368-4b16-bdcd-d46a7e34adb7
-- title:
--   (3.13), p. 180 — ‖d_{k+1}‖²/(g_{k+1}ᵀd_{k+1})² ≤ ‖d_k‖²/(g_kᵀd_k)² + 1/‖g_{k+1}‖²
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, $\sigma<1$, and let $(x_k,d_k,\alpha_k)_{k\ge1}$ be a non-terminating run of Algorithm 2.1 (standard Wolfe steps with constants $\delta,\sigma$, and $g_k\neq0$ for every $k\ge1$). Then for every $k\ge1$
--   $$\frac{\|d_{k+1}\|^2}{(g_{k+1}^Td_{k+1})^2}=\frac{\|d_k\|^2}{(g_k^Td_k)^2}-\frac{2}{g_{k+1}^Td_{k+1}}-\frac{\|g_{k+1}\|^2}{(g_{k+1}^Td_{k+1})^2}
--   =\frac{\|d_k\|^2}{(g_k^Td_k)^2}-\Big(\frac{1}{\|g_{k+1}\|}+\frac{\|g_{k+1}\|}{g_{k+1}^Td_{k+1}}\Big)^2+\frac{1}{\|g_{k+1}\|^2}$$
--   and consequently
--   $$\frac{\|d_{k+1}\|^2}{(g_{k+1}^Td_{k+1})^2}\le\frac{\|d_k\|^2}{(g_k^Td_k)^2}+\frac{1}{\|g_{k+1}\|^2}.$$
--
--   This recurrence for the reciprocal of the Zoutendijk term $(g_k^Td_k)^2/\|d_k\|^2$ is what makes the Dai–Yuan analysis short: it involves a single sequence.
--
--   **Formalization Note** Assumption 3.1 and $\delta>0$ are not used and are dropped. The quotients are Lean divisions; all denominators are nonzero along a non-terminating run ($g_k\neq0$ by hypothesis, $g_k^Td_k<0$ by (3.9)), and no guard is added.
-- source:
--   Dai and Yuan, A nonlinear conjugate gradient method with a strong global convergence property, SIAM J. Optim. 10 (1999), p. 180, (3.11)–(3.13), proof of Theorem 3.3

import Mathlib
import Definitions.Def_DaiYuanCG_Conv_Setting

namespace DaiYuanCG.Conv

theorem eq_3_13 {n : ℕ} (f : E n → ℝ) (δ σ : ℝ) (hσ1 : σ < 1)
    (x d : ℕ → E n) (α : ℕ → ℝ) (hrun : IsDYRun f δ σ x d α)
    (hnt : ∀ k, 1 ≤ k → gradient f (x k) ≠ 0) :
    ∀ k, 1 ≤ k →
      ‖d (k + 1)‖ ^ 2 / inner ℝ (gradient f (x (k + 1))) (d (k + 1)) ^ 2 =
          ‖d k‖ ^ 2 / inner ℝ (gradient f (x k)) (d k) ^ 2
            - 2 / inner ℝ (gradient f (x (k + 1))) (d (k + 1))
            - ‖gradient f (x (k + 1))‖ ^ 2 /
                inner ℝ (gradient f (x (k + 1))) (d (k + 1)) ^ 2 ∧
      ‖d (k + 1)‖ ^ 2 / inner ℝ (gradient f (x (k + 1))) (d (k + 1)) ^ 2 =
          ‖d k‖ ^ 2 / inner ℝ (gradient f (x k)) (d k) ^ 2
            - (1 / ‖gradient f (x (k + 1))‖ + ‖gradient f (x (k + 1))‖ /
                inner ℝ (gradient f (x (k + 1))) (d (k + 1))) ^ 2
            + 1 / ‖gradient f (x (k + 1))‖ ^ 2 ∧
      ‖d (k + 1)‖ ^ 2 / inner ℝ (gradient f (x (k + 1))) (d (k + 1)) ^ 2 ≤
          ‖d k‖ ^ 2 / inner ℝ (gradient f (x k)) (d k) ^ 2
            + 1 / ‖gradient f (x (k + 1))‖ ^ 2 := by sorry

end DaiYuanCG.Conv
