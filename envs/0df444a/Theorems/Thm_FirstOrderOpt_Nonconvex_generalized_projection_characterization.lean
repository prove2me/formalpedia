-- Prove2me | Theorems.Thm_FirstOrderOpt_Nonconvex_generalized_projection_characterization
-- name    : FirstOrderOpt.Nonconvex.generalized_projection_characterization
-- status  : Disproved
-- author  : @mikedeng1
-- created : 2026-09-19T21:03:02.472984+00:00
-- url     : https://prove2.me/theorems/6b663b8c-a0b1-4bf4-b409-935f8ccfae83
-- title:
--   Lemma 6.6 — characterization of the generalized projection
-- statement:
--   With $x^+$ the generalized projection of (6.2.6) (see `generalized_projection_gradient_bound`
--   for the setup), Lemma 6.6 gives the three-point characterization analogous to Lemma 3.4 of
--   Chapter 3, now with the extra nonsmooth term $h$:
--
--   **Lemma 6.6.** For every $u \in X$,
--   $$\langle g,x^+\rangle + h(x^+) + \tfrac1\gamma V(x,x^+) \le \langle g,u\rangle + h(u) +
--   \tfrac1\gamma\big[V(x,u) - V(x^+,u)\big].$$
--
--   The book notes this proof is "a special case of Lemma 3.5" (the general prox-mapping
--   characterization lemma of Chapter 3, stated there for a sum of two Bregman terms with weights
--   $\mu_1,\mu_2\ge0$; here $\mu_1=1,\mu_2=0$ with the extra $h(\cdot)$ folded in). It is the tool
--   used to establish part (b) of Theorem 6.6 (the convex-case corollary, out of scope for this
--   mission).
--
--   **Formalization Note.** Same setup and conventions as `generalized_projection_gradient_bound`:
--   real inner product space, `x+`'s minimality stated pointwise.
-- source:
--   Lan, First-order and Stochastic Optimization Methods for Machine Learning, Springer 2020, p. 329, Lemma 6.6

import Mathlib

namespace FirstOrderOpt.Nonconvex

open scoped RealInnerProductSpace

/-- Lemma 6.6. `xPlus` is the generalized projection (6.2.6). Then for every `u ∈ X`,
`⟨g,xPlus⟩ + h(xPlus) + (1/γ)V(x,xPlus) ≤ ⟨g,u⟩ + h(u) + (1/γ)[V(x,u) - V(xPlus,u)]`. -/
theorem generalized_projection_characterization {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] (X : Set E) (h : E → ℝ) (V : E → E → ℝ)
    (x xPlus g : E) (γ : ℝ) (hγ : 0 < γ) (hx : x ∈ X) (hxPlus : xPlus ∈ X)
    (hmin : ∀ u ∈ X, ⟪g, xPlus⟫ + (1 / γ) * V x xPlus + h xPlus ≤
      ⟪g, u⟫ + (1 / γ) * V x u + h u) :
    ∀ u ∈ X, ⟪g, xPlus⟫ + h xPlus + (1 / γ) * V x xPlus ≤
      ⟪g, u⟫ + h u + (1 / γ) * (V x u - V xPlus u) := by sorry

end FirstOrderOpt.Nonconvex
