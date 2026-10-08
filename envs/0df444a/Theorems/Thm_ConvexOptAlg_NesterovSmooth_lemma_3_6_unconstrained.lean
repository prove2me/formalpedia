-- Prove2me | Theorems.Thm_ConvexOptAlg_NesterovSmooth_lemma_3_6_unconstrained
-- name    : ConvexOptAlg.NesterovSmooth.lemma_3_6_unconstrained
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T17:55:10.249412+00:00
-- url     : https://prove2.me/theorems/67ebfccc-d731-4144-bcc4-a316c36fe432
-- title:
--   Lemma 3.6, p. 270, unconstrained (X = ℝⁿ) — f(x − ∇f(x)/β) − f(y) ≤ ∇f(x)⊤(x − y) − ‖∇f(x)‖²/(2β)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be convex and $\beta$-smooth with $\beta>0$. Then for all $x,y\in\mathbb R^n$,
--
--   $$f\Bigl(x-\frac1\beta\nabla f(x)\Bigr)-f(y)\le\nabla f(x)^\top(x-y)-\frac1{2\beta}\|\nabla f(x)\|^2.$$
--
--   This is Lemma 3.6 of the book in the case $\mathcal X=\mathbb R^n$: the projection $\Pi_{\mathcal X}$ is the identity, so $x^+=x-\frac1\beta\nabla f(x)$ and the gradient mapping $g_{\mathcal X}(x)=\beta(x-x^+)$ equals $\nabla f(x)$. The proof of Theorem 3.19 applies it twice per iteration, once with $y=y_s$ and once with $y=x^*$.
--
--   **Formalization Note** The gradient is an explicit map $g$ with $g(x)=\nabla f(x)$; convexity is Mathlib's `ConvexOn ℝ Set.univ f`. The hypothesis $\beta>0$ is implicit in the book (the step $1/\beta$) and is stated.
-- source:
--   Bubeck, arXiv:1405.4980v2, Lemma 3.6, p. 270, in the unconstrained form used in the proof of Theorem 3.19, p. 294

import Mathlib
import Definitions.Def_ConvexOptAlg_NesterovSmooth_Defs
open scoped InnerProductSpace

namespace ConvexOptAlg.NesterovSmooth

/-- Lemma 3.6 (Bubeck, arXiv:1405.4980v2, p. 270) in its unconstrained version (X = ℝⁿ), as used in
the proof of Theorem 3.19 (p. 294): for a convex β-smooth `f` on `ℝⁿ` with gradient map `g`,
`x⁺ = x − (1/β)∇f(x)` and `g_X(x) = β(x − x⁺) = ∇f(x)`, for all `x, y`,
`f(x⁺) − f(y) ≤ ∇f(x)⊤(x − y) − (1/(2β))‖∇f(x)‖²`. -/
theorem lemma_3_6_unconstrained {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n)) (β : ℝ) (hβ : 0 < β)
    (hconv : ConvexOn ℝ Set.univ f) (hf : IsBetaSmooth f g β) (x y : EuclideanSpace ℝ (Fin n)) :
    f (x - (1 / β) • g x) - f y ≤ ⟪g x, x - y⟫_ℝ - 1 / (2 * β) * ‖g x‖ ^ 2 := by sorry

end ConvexOptAlg.NesterovSmooth
