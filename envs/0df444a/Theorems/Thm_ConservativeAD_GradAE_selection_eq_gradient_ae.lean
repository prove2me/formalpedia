-- Prove2me | Theorems.Thm_ConservativeAD_GradAE_selection_eq_gradient_ae
-- name    : ConservativeAD.GradAE.selection_eq_gradient_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:13.717886+00:00
-- url     : https://prove2.me/theorems/05a54c9c-f74a-4320-acc8-2011214cc169
-- title:
--   Proof of Theorem 1 — a measurable selection $a$ of $D$ equals $\nabla f$ almost everywhere
-- statement:
--   Let $D:\mathbb R^p\rightrightarrows\mathbb R^p$ be a conservative field, $f$ a locally Lipschitz potential for $D$, and $a$ a Borel measurable selection of $D$. Then for Lebesgue-almost every $y\in\mathbb R^p$, $f$ is differentiable at $y$ and
--
--   $$
--   a(y)=\nabla f(y) .
--   $$
--
--   This is the last step of the proof of Theorem 1 for a single selection; Theorem 1 follows by applying it to a countable family of selections whose values are dense in each $D(y)$.
--
--   **Formalization Note** `gradient f y` is $0$ where $f$ is not differentiable, so differentiability at $y$ is stated explicitly. Local Lipschitz continuity (not global) is assumed, as in the paper.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 9, §3.1, proof of Theorem 1, last sentence of the page

import Mathlib
import Definitions.Def_ConservativeAD_GradAE_ConservativeField
open MeasureTheory

namespace ConservativeAD.GradAE

/-- §3.1, proof of Theorem 1: for a locally Lipschitz potential `f` of `D` and a (Borel)
measurable selection `a` of `D`, for Lebesgue-almost every `y`, `f` is differentiable at `y`
and `a y = ∇f(y)`. -/
theorem selection_eq_gradient_ae {p : ℕ}
    (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (f : EuclideanSpace ℝ (Fin p) → ℝ) (hD : IsPotential D f) (hf : LocallyLipschitz f)
    (a : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (ha : Measurable a)
    (haD : ∀ y, a y ∈ D y) :
    ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin p))),
      DifferentiableAt ℝ f y ∧ a y = gradient f y := by sorry

end ConservativeAD.GradAE
