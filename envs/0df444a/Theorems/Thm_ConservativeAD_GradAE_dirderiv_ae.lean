-- Prove2me | Theorems.Thm_ConservativeAD_GradAE_dirderiv_ae
-- name    : ConservativeAD.GradAE.dirderiv_ae
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:41:02.758175+00:00
-- url     : https://prove2.me/theorems/b8867938-19bb-421a-8a7e-f322156d4673
-- title:
--   Proof of Theorem 1 — $f'(y;v)=\langle v,a(y)\rangle$ for almost all $y\in\mathbb R^p$
-- statement:
--   Let $D:\mathbb R^p\rightrightarrows\mathbb R^p$ be a conservative field, $f$ a potential for $D$, $a$ a Borel measurable selection of $D$, and fix a direction $v\in\mathbb R^p$. Then for Lebesgue-almost every $y\in\mathbb R^p$ the directional derivative $f'(y;v)=\lim_{r\to0,\,r\ne0}\frac{f(y+rv)-f(y)}{r}$ exists and
--
--   $$
--   f'(y;v)=\langle v,a(y)\rangle .
--   $$
--
--   This upgrades equation (6) from almost every point of every line parallel to $v$ to almost every point of $\mathbb R^p$ (the paper uses Fubini's theorem).
--
--   **Formalization Note** The existence of the two-sided limit with this value is stated as `HasDerivAt (fun r => f (y + r • v)) ⟪v, a y⟫ 0`; "almost every $y$" refers to `volume` on `EuclideanSpace ℝ (Fin p)`, which is Lebesgue measure.
-- source:
--   Bolte, Pauwels, Conservative set valued fields, automatic differentiation, stochastic gradient methods and deep learning, TSE Working Paper 1044 (October 2019), p. 9, §3.1, proof of Theorem 1, 'Fubini's theorem entails that A has zero Lebesgue measure'

import Mathlib
import Definitions.Def_ConservativeAD_GradAE_ConservativeField
open MeasureTheory

namespace ConservativeAD.GradAE

/-- §3.1, proof of Theorem 1: for a potential `f` of `D`, a (Borel) measurable selection `a`
of `D` and a fixed direction `v`, the directional derivative `f'(y; v)` exists and equals
`⟨v, a y⟩` for Lebesgue-almost every `y ∈ ℝ^p`. -/
theorem dirderiv_ae {p : ℕ} (D : EuclideanSpace ℝ (Fin p) → Set (EuclideanSpace ℝ (Fin p)))
    (f : EuclideanSpace ℝ (Fin p) → ℝ) (hD : IsPotential D f)
    (a : EuclideanSpace ℝ (Fin p) → EuclideanSpace ℝ (Fin p)) (ha : Measurable a)
    (haD : ∀ y, a y ∈ D y) (v : EuclideanSpace ℝ (Fin p)) :
    ∀ᵐ y ∂(volume : Measure (EuclideanSpace ℝ (Fin p))),
      HasDerivAt (fun r : ℝ => f (y + r • v)) (inner ℝ v (a y)) 0 := by sorry

end ConservativeAD.GradAE
