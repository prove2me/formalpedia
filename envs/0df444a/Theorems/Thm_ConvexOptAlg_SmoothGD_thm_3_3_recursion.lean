-- Prove2me | Theorems.Thm_ConvexOptAlg_SmoothGD_thm_3_3_recursion
-- name    : ConvexOptAlg.SmoothGD.thm_3_3_recursion
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:05:44.780991+00:00
-- url     : https://prove2.me/theorems/21b74f38-f100-4e1c-b668-da74c9bc86c9
-- title:
--   §3.2, proof of Theorem 3.3, p. 268 — the gaps δ_s satisfy δ_{s+1} ≤ δ_s − δ_s²/(2β‖x₁ − x*‖²)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth with $\beta>0$, let $x^*$ be a minimizer of $f$, and let $(x_s)_{s\ge1}$ be gradient descent with $\eta=1/\beta$. Write $\delta_s=f(x_s)-f(x^*)$. Then for every $s\ge1$,
--
--   $$\delta_s^2\le 2\beta\|x_1-x^*\|^2\,(\delta_s-\delta_{s+1}),$$
--
--   that is, when $x_1\ne x^*$,
--   $$\delta_{s+1}\le\delta_s-\frac{1}{2\beta\|x_1-x^*\|^2}\,\delta_s^2.$$
--
--   This one-step recursion on the optimality gaps is what the proof of Theorem 3.3 turns into the $1/(t-1)$ rate.
--
--   **Formalization Note** The page writes the recursion with $\|x_1-x^*\|^2$ in a denominator; the Lean statement is multiplied through by $2\beta\|x_1-x^*\|^2$, which is equivalent when $x_1\ne x^*$ and remains true (with both sides $0$) when $x_1=x^*$. The minimizer's existence is the book's standing assumption; $\beta>0$ is implicit ($\eta=1/\beta$).
-- source:
--   Bubeck, arXiv:1405.4980v2, §3.2, proof of Theorem 3.3, last display on p. 268

import Mathlib
import Definitions.Def_ConvexOptAlg_SmoothGD_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.SmoothGD

/-- Proof of Theorem 3.3, last display on p. 268 (Bubeck, arXiv:1405.4980v2), multiplied out: for
gradient descent with `η = 1/β` on a convex β-smooth `f` (β > 0) with a minimizer `x*`, writing
`δ_s = f(x_s) − f(x*)`, for every `s ≥ 1`,
`δ_s² ≤ 2β‖x₁ − x*‖² (δ_s − δ_{s+1})`, i.e. `δ_{s+1} ≤ δ_s − δ_s²/(2β‖x₁ − x*‖²)` when `x₁ ≠ x*`;
the multiplied form also covers `x₁ = x*`. -/
theorem thm_3_3_recursion {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β)
    (xstar : EuclideanSpace ℝ (Fin n)) (hmin : ∀ y, f xstar ≤ f y)
    (x : ℕ → EuclideanSpace ℝ (Fin n)) (hrun : IsGDRun g (1 / β) x) (s : ℕ) (hs : 1 ≤ s) :
    (f (x s) - f xstar) ^ 2 ≤
      2 * β * ‖x 1 - xstar‖ ^ 2 * ((f (x s) - f xstar) - (f (x (s + 1)) - f xstar)) := by sorry

end ConvexOptAlg.SmoothGD
