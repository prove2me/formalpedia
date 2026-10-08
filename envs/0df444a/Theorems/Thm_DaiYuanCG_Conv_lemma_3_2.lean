-- Prove2me | Theorems.Thm_DaiYuanCG_Conv_lemma_3_2
-- name    : DaiYuanCG.Conv.lemma_3_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T17:01:12.752094+00:00
-- url     : https://prove2.me/theorems/9587174a-f89e-42ef-b1e6-3a509cde1377
-- title:
--   Lemma 3.2, p. 179 — Zoutendijk condition Σ_{k≥1} (g_kᵀd_k)²/‖d_k‖² < ∞ for descent directions with standard Wolfe steps
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ and let $0<\delta<\sigma<1$. Suppose Assumption 3.1 holds at $x_1$ with neighbourhood $\mathcal N$ and Lipschitz constant $L>0$ ($f$ bounded below on $\mathbb R^n$, continuously differentiable on an open $\mathcal N\supseteq\{x:f(x)\le f(x_1)\}$, with $L$-Lipschitz gradient on $\mathcal N$). Consider any method $x_{k+1}=x_k+\alpha_kd_k$ ($k\ge1$) where $\alpha_k>0$, $d_k$ is a descent direction ($g_k^Td_k<0$) and $\alpha_k$ satisfies the standard Wolfe conditions (1.7) and (1.10). Then
--   $$\sum_{k\ge1}\frac{(g_k^Td_k)^2}{\|d_k\|^2}<\infty .$$
--
--   This is the Zoutendijk condition, essentially due to Zoutendijk and Wolfe. It holds for every descent method with Wolfe line searches and is the only place where the assumptions on $f$ enter the convergence proof of Theorem 3.3.
--
--   **Formalization Note** Since the terms are nonnegative, "$<\infty$" is stated as summability of $k\mapsto(g_{k+1}^Td_{k+1})^2/\|d_{k+1}\|^2$ over $k\ge0$, i.e. of the paper's series over $k\ge1$; index $0$ is unconstrained. The level set need not be bounded, and the Lipschitz bound is only required on $\mathcal N$.
-- source:
--   Dai and Yuan, A nonlinear conjugate gradient method with a strong global convergence property, SIAM J. Optim. 10 (1999), p. 179, Lemma 3.2 and (3.2)

import Mathlib
import Definitions.Def_DaiYuanCG_Conv_Setting

namespace DaiYuanCG.Conv

theorem lemma_3_2 {n : ℕ} (f : E n → ℝ) (N : Set (E n)) (L : ℝ)
    (δ σ : ℝ) (hδ : 0 < δ) (hδσ : δ < σ) (hσ1 : σ < 1)
    (x d : ℕ → E n) (α : ℕ → ℝ) (hA : Assumption31 f (x 1) N L)
    (hm : IsDescentWolfeMethod f δ σ x d α) :
    Summable (fun k : ℕ =>
      inner ℝ (gradient f (x (k + 1))) (d (k + 1)) ^ 2 / ‖d (k + 1)‖ ^ 2) := by sorry

end DaiYuanCG.Conv
