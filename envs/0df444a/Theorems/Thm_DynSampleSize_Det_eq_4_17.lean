-- Prove2me | Theorems.Thm_DynSampleSize_Det_eq_4_17
-- name    : DynSampleSize.Det.eq_4_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:44.043988+00:00
-- url     : https://prove2.me/theorems/f8f3454a-fe16-4550-b821-7a99438bf7e6
-- title:
--   (4.17) — under (4.8) at every iteration, $J(w_k) \le (1-\beta\lambda/L)^k J(w_0)$
-- statement:
--   Let $J : \mathbb{R}^m \to \mathbb{R}$ satisfy assumption (4.2) with constants $0<\lambda<L$, and let $w_*$ be its minimizer, normalized so that $J(w_*) = 0$. Let $\theta \in (0,1)$, let $(g_k)$ be arbitrary vectors and let $w_{k+1} = w_k - \frac{1-\theta}{L} g_k$ (iteration (4.1) with steplength (4.7)). If the relative-error condition (4.8), $\|g_j - \nabla J(w_j)\| \le \theta\|g_j\|$, holds at every iteration $j < k$, then
--
--   $$
--   J(w_k) \;\le\; \Bigl(1 - \frac{\beta\lambda}{L}\Bigr)^{k} J(w_0), \qquad \beta = \frac{(1-\theta)^2}{2(1+\theta)^2}.
--   $$
--
--   This is the linear convergence of the function values, from which (4.10), (4.11) and (4.12) of Theorem 4.1 follow.
--
--   **Formalization Note** The paper assumes (4.8) "at every iteration"; the Lean statement assumes it only for the iterations $j < k$ that precede $w_k$, which is a slightly stronger statement implied by the same proof.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 9, (4.17)

import Mathlib
import Definitions.Def_DynSampleSize_Det_Setting

open Filter Topology

namespace DynSampleSize.Det

theorem eq_4_17 {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : HessianBounds J lam L) (wstar : EuclideanSpace ℝ (Fin m))
    (hmin : ∀ w, J wstar ≤ J w) (hJstar : J wstar = 0)
    (θ : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1) (g w : ℕ → EuclideanSpace ℝ (Fin m))
    (hw : ∀ k, w (k + 1) = w k - ((1 - θ) / L) • g k) (k : ℕ)
    (h48 : ∀ j < k, ‖g j - gradient J (w j)‖ ≤ θ * ‖g j‖) :
    J (w k) ≤ (1 - beta θ * lam / L) ^ k * J (w 0) := by sorry

end DynSampleSize.Det
