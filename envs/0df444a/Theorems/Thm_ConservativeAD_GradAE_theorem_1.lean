-- Prove2me | Theorems.Thm_ConservativeAD_GradAE_theorem_1
-- name    : ConservativeAD.GradAE.theorem_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:23.082552+00:00
-- url     : https://prove2.me/theorems/129fecca-1b89-4208-bf22-b871e17cfff3
-- title:
--   Theorem 1 — a conservative field equals $\{\nabla f\}$ Lebesgue-almost everywhere
-- statement:
--   Let $D:\mathbb R^p\rightrightarrows\mathbb R^p$ be a conservative field and let $f:\mathbb R^p\to\mathbb R$ be a (locally Lipschitz continuous) potential for $D$. Then for Lebesgue-almost every $x\in\mathbb R^p$, $f$ is differentiable at $x$ and
--
--   $$
--   D(x)=\{\nabla f(x)\} .
--   $$
--
--   So a conservative field, although set-valued, is single-valued and equal to the gradient of its potential outside a Lebesgue-null set. This is the basic structural fact of the conservative-field calculus: it identifies the Clarke subdifferential as the minimal convex-valued conservative field for $f$ and underlies the convergence analysis of stochastic subgradient methods driven by automatic differentiation.
--
--   **Formalization Note** $D(x)=\{\nabla f(x)\}$ is set equality (the value is the singleton, not merely a set containing $\nabla f(x)$). Differentiability at $x$ is stated explicitly because Lean's `gradient` returns $0$ at points of non-differentiability. The local Lipschitz hypothesis is kept as printed, although Remark 3(d) shows it follows from the potential hypothesis. Potentials are determined only up to an additive constant and the statement holds for each of them.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 9, Theorem 1

import Mathlib
import Definitions.Def_ConservativeAD_GradAE_ConservativeField
open MeasureTheory

namespace ConservativeAD.GradAE

/-- Theorem 1 (a conservative field is a gradient almost everywhere): if `D` is a conservative
field and `f` a (locally Lipschitz continuous) potential for `D`, then for Lebesgue-almost every
`x ∈ ℝ^p`, `f` is differentiable at `x` and `D x = {∇f(x)}`. -/
theorem theorem_1 {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (f : EuclideanSpace ℝ (Fin p) → ℝ) (hD : IsPotential D f) (hf : LocallyLipschitz f) :
    ∀ᵐ x ∂(volume : Measure (EuclideanSpace ℝ (Fin p))),
      DifferentiableAt ℝ f x ∧ D x = {gradient f x} := by sorry

end ConservativeAD.GradAE
