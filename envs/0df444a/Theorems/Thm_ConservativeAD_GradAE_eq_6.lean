-- Prove2me | Theorems.Thm_ConservativeAD_GradAE_eq_6
-- name    : ConservativeAD.GradAE.eq_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:40:58.278905+00:00
-- url     : https://prove2.me/theorems/06d40325-e248-4e58-96da-51c8e801ceb8
-- title:
--   Proof of Theorem 1, (6) — $f'(y;v)=\langle v,a(y)\rangle$ almost everywhere on each line $x+\mathbb Rv$
-- statement:
--   Let $D:\mathbb R^p\rightrightarrows\mathbb R^p$ be a conservative field, $f$ a potential for $D$, and $a$ a Borel measurable selection of $D$. For $y,v\in\mathbb R^p$ write
--
--   $$
--   f'(y;v):=\lim_{r\to0,\ r\neq0}\frac{f(y+rv)-f(y)}{r}
--   $$
--
--   when the limit exists. Then for every $x,v\in\mathbb R^p$ and Lebesgue-almost every $\tau\in\mathbb R$, the limit $f'(x+\tau v;v)$ exists and
--
--   $$
--   f'(x+\tau v;v)=\langle v,a(x+\tau v)\rangle . \tag{6}
--   $$
--
--   This is equation (6) of the paper: the directional derivative of the potential agrees with the selection almost everywhere on each line parallel to $v$.
--
--   **Formalization Note** "Almost everywhere on the line $x+\mathbb Rv$" is expressed through the parametrisation $\tau\mapsto x+\tau v$ with Lebesgue measure on $\mathbb R$, and the existence of the two-sided limit with value $\langle v,a(x+\tau v)\rangle$ is stated as `HasDerivAt (fun r => f (x + r • v)) ⟪v, a (x + τ • v)⟫ τ`.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 9, §3.1, proof of Theorem 1, (6)

import Mathlib
import Definitions.Def_ConservativeAD_GradAE_ConservativeField
open MeasureTheory

namespace ConservativeAD.GradAE

/-- §3.1, proof of Theorem 1, (6): for a potential `f` of `D` and a (Borel) measurable selection
`a` of `D`, on every line `x + ℝ v` the directional derivative `f'(y; v)` (two-sided) exists and
equals `⟨v, a y⟩` at `y = x + τ v` for Lebesgue-almost every `τ`. -/
theorem eq_6 {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (f : EuclideanSpace ℝ (Fin p) → ℝ) (hD : IsPotential D f)
    (a : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (ha : Measurable a)
    (haD : ∀ y, a y ∈ D y) :
    ∀ x v : EuclideanSpace ℝ (Fin p), ∀ᵐ τ : ℝ,
      HasDerivAt (fun r : ℝ => f (x + r • v)) (inner ℝ v (a (x + τ • v))) τ := by sorry

end ConservativeAD.GradAE
