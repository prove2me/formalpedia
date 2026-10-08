-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovSmooth_eq_3_25
-- name    : ConvexOptAlg.NesterovSmooth.eq_3_25
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:56:08.73383+00:00
-- url     : https://prove2.me/theorems/72507582-a595-4c32-b66c-1fa49c09be68
-- title:
--   Eq. (3.25), pp. 294–295 — λ²_sδ_{s+1} − λ²_{s−1}δ_s ≤ (β/2)(‖λ_sx_s − (λ_s − 1)y_s − x*‖² − ‖λ_sy_{s+1} − (λ_s − 1)y_s − x*‖²)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth with $\beta>0$, let $x^*$ be a minimizer of $f$, and let $(x_t),(y_t)$ be a run of Nesterov's accelerated gradient descent for the smooth case, with step sequence $(\lambda_t)$. Write $\delta_s=f(y_s)-f(x^*)$. Then for every $s\ge1$,
--
--   $$\lambda_s^2\delta_{s+1}-\lambda_{s-1}^2\delta_s\le\frac\beta2\Bigl(\|\lambda_sx_s-(\lambda_s-1)y_s-x^*\|^2-\|\lambda_sy_{s+1}-(\lambda_s-1)y_s-x^*\|^2\Bigr).$$
--
--   This is the one-step inequality of the proof: the weighted optimality gap decreases by at most a difference of two squared distances.
--
--   **Formalization Note** The first member and the last member of the book's chain (3.25) are stated; the intermediate expression is omitted. $x^*$ a minimizer is the book's standing assumption; $\beta>0$ is stated.
-- source:
--   Bubeck, arXiv:1405.4980v2, proof of Theorem 3.19, Eq. (3.25), pp. 294–295

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovSmooth

/-- Eq. (3.25) (Bubeck, arXiv:1405.4980v2, proof of Theorem 3.19, pp. 294–295): along a run of
Nesterov's accelerated gradient descent on a convex β-smooth `f` with minimizer `x*`, writing
`δ_s = f(y_s) − f(x*)`, for every `s ≥ 1`,
`λ_s²δ_{s+1} − λ_{s−1}²δ_s ≤ (β/2)(‖λ_s x_s − (λ_s − 1)y_s − x*‖² − ‖λ_s y_{s+1} − (λ_s − 1)y_s − x*‖²)`. -/
theorem eq_3_25 {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ z, f xstar ≤ f z)
    (x y : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsNesterovRun g β x y) (s : ℕ) (hs : 1 ≤ s) :
    lam s ^ 2 * (f (y (s + 1)) - f xstar) - lam (s - 1) ^ 2 * (f (y s) - f xstar) ≤
      β / 2 * (‖lam s • x s - (lam s - 1) • y s - xstar‖ ^ 2 -
        ‖lam s • y (s + 1) - (lam s - 1) • y s - xstar‖ ^ 2) := by sorry

end ConvexOptAlg.NesterovSmooth
