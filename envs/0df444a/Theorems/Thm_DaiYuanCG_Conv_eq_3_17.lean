-- Prove2me | Theorems.Thm_DaiYuanCG_Conv_eq_3_17
-- name    : DaiYuanCG.Conv.eq_3_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:23.642677+00:00
-- url     : https://prove2.me/theorems/ea47e10e-b027-4d32-b545-96bddf0b3881
-- title:
--   (3.16)–(3.17), p. 181 — if ‖g_k‖ ≥ c > 0 for all k, then ‖d_k‖²/(g_kᵀd_k)² ≤ k/c² and Σ (g_kᵀd_k)²/‖d_k‖² = ∞
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$, $\sigma<1$, and let $(x_k,d_k,\alpha_k)_{k\ge1}$ be a non-terminating run of Algorithm 2.1 (standard Wolfe steps with constants $\delta,\sigma$, and $g_k\neq0$ for every $k\ge1$). Suppose there is a constant $c>0$ with $\|g_k\|\ge c$ for all $k\ge1$ (this is (3.15)). Then
--   $$\frac{\|d_k\|^2}{(g_k^Td_k)^2}\le\frac{k}{c^2}\quad\text{for all }k\ge1,\qquad\text{and}\qquad\sum_{k\ge1}\frac{(g_k^Td_k)^2}{\|d_k\|^2}=\infty .$$
--
--   This is the contrapositive half of the proof of Theorem 3.3: gradients bounded away from zero force the Zoutendijk series to diverge, contradicting Lemma 3.2.
--
--   **Formalization Note** Assumption 3.1 and $\delta>0$ are not used and are dropped. Since the terms are nonnegative, "$=\infty$" is stated as non-summability of $k\mapsto (g_{k+1}^Td_{k+1})^2/\|d_{k+1}\|^2$ over $k\ge0$, i.e. of the paper's series over $k\ge1$.
-- source:
--   Dai and Yuan, A nonlinear conjugate gradient method with a strong global convergence property, SIAM J. Optim. 10 (1999), pp. 180–181, (3.15)–(3.17), proof of Theorem 3.3

import Mathlib
import Definitions.Def_DaiYuanCG_Conv_Setting

namespace DaiYuanCG.Conv

theorem eq_3_17 {n : ℕ} (f : E n → ℝ) (δ σ : ℝ) (hσ1 : σ < 1)
    (x d : ℕ → E n) (α : ℕ → ℝ) (hrun : IsDYRun f δ σ x d α)
    (hnt : ∀ k, 1 ≤ k → gradient f (x k) ≠ 0)
    (c : ℝ) (hc : 0 < c) (hgc : ∀ k, 1 ≤ k → c ≤ ‖gradient f (x k)‖) :
    (∀ k, 1 ≤ k → ‖d k‖ ^ 2 / inner ℝ (gradient f (x k)) (d k) ^ 2 ≤ (k : ℝ) / c ^ 2) ∧
      ¬ Summable (fun k : ℕ =>
        inner ℝ (gradient f (x (k + 1))) (d (k + 1)) ^ 2 / ‖d (k + 1)‖ ^ 2) := by sorry

end DaiYuanCG.Conv
