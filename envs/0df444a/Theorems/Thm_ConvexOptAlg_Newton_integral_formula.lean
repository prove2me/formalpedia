-- Prove2me | Theorems.Thm_ConvexOptAlg_Newton_integral_formula
-- name    : ConvexOptAlg.Newton.integral_formula
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-05T18:33:05.013641+00:00
-- url     : https://prove2.me/theorems/c2641889-081d-4da2-971d-de8da51bdd5f
-- title:
--   §5.3.2, proof of Theorem 5.3, p. 321 — ∫₀¹ ∇²f(x + sh) h ds = ∇f(x + h) − ∇f(x)
-- statement:
--   Let $f:\mathbb R^n\to\mathbb R$ be a $C^2$ function with gradient $\nabla f$ and Hessian $\nabla^2 f$. Then for all $x,h\in\mathbb R^n$,
--
--   $$\int_0^1 \nabla^2 f(x+sh)\,h\,ds=\nabla f(x+h)-\nabla f(x).$$
--
--   This is the fundamental theorem of calculus applied to the gradient along the segment from $x$ to $x+h$. It is the first step of the local analysis of Newton's method, where it expresses the gradient at an iterate through Hessians along the segment to the minimizer.
--
--   **Formalization Note** The integral is the Bochner integral of the $\mathbb R^n$-valued map $s\mapsto\nabla^2 f(x+sh)h$ over $[0,1]$ (`intervalIntegral`). $\mathbb R^n$ is `EuclideanSpace ℝ (Fin n)`; the gradient and the Hessian are the explicit maps of the definition item.
-- source:
--   Bubeck, arXiv:1405.4980v2, §5.3.2, proof of Theorem 5.3, p. 321, first display

import Mathlib
import Definitions.Def_ConvexOptAlg_Newton_Defs

namespace ConvexOptAlg.Newton

/-- The integral formula in the proof of Theorem 5.3 (Bubeck, arXiv:1405.4980v2, §5.3.2, p. 321,
first display of the proof): for a C² function `f : ℝⁿ → ℝ` with gradient map `g` and Hessian map
`H`, and for all `x, h ∈ ℝⁿ`, `∫₀¹ ∇²f(x + s h) h ds = ∇f(x + h) − ∇f(x)`. The integral is the
Bochner integral of an `ℝⁿ`-valued function over `[0, 1]`. -/
theorem integral_formula {n : ℕ} (f : EuclideanSpace ℝ (Fin n) → ℝ)
    (g : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (H : EuclideanSpace ℝ (Fin n) → (EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n)))
    (hfgH : IsC2GradHess f g H) (x h : EuclideanSpace ℝ (Fin n)) :
    ∫ s in (0 : ℝ)..1, H (x + s • h) h = g (x + h) - g x := by sorry

end ConvexOptAlg.Newton
