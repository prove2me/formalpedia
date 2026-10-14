-- Prove2me | Theorems.Thm_DbarRegularity_inv_sq_kernel_conditions
-- name    : DbarRegularity.inv_sq_kernel_conditions
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T20:32:20.777609+00:00
-- url     : https://prove2.me/theorems/78207957-00ed-4b24-ab9e-e9cc8bc1a649
-- title:
--   The kernel 1/z^2 on the plane satisfies the standard singular-integral conditions
-- statement:
--   Identify $y=(y_0,y_1)\in\mathbb R^2$ with $z=y_0+iy_1\in\mathbb C$ and let $K(y)=1/z^2$ (with $K(0)=0$). There is a constant $B$ such that $K$ is measurable and
--   1. $|K(x)|\le B\,|x|^{-2}$ for $x\ne0$;
--   2. $\displaystyle\int_{|x|\ge 2|y|}|K(x-y)-K(x)|\,dx\le B$ for every $y\ne0$;
--   3. $\displaystyle\int_{R_1<|x|<R_2}K(x)\,dx=0$ for all $0<R_1<R_2$.
--
--   These are the size, Hörmander and cancellation conditions (18)–(19) of Stein, Chapter II, § 3.2, for $d=2$.
--
--   **Formalization Note.** $\mathbb R^2$ is `EuclideanSpace ℝ (Fin 2)`; the kernel is any `K` with `K y = 1 / ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ^ 2` for all `y` (so `K 0 = 0` by Lean's convention `1 / 0 = 0`); measurability is `AEStronglyMeasurable K volume`, condition 2 is a lower Lebesgue integral bounded by `ENNReal.ofReal B`, and condition 3 is a Bochner set integral.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter III, § 1.3, Proposition 4, p. 60

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.Complex.Isometry
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Complex.Circle
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.Analysis.Calculus.Deriv.ZPow

namespace DbarRegularity

open MeasureTheory Metric Set
open scoped ENNReal ContDiff

/-- The kernel `1 / (y₀ + i y₁)²` on `ℝ²` satisfies Stein's size, Hörmander and cancellation
conditions for some constant `B`. -/
theorem inv_sq_kernel_conditions (K : EuclideanSpace ℝ (Fin 2) → ℂ)
    (hK : ∀ y, K y = 1 / ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ^ 2) :
    ∃ B : ℝ, AEStronglyMeasurable K volume ∧
      (∀ x, x ≠ 0 → ‖K x‖ ≤ B / ‖x‖ ^ 2) ∧
      (∀ y, y ≠ 0 → ∫⁻ x in {x | 2 * ‖y‖ ≤ ‖x‖}, ‖K (x - y) - K x‖ₑ ≤ ENNReal.ofReal B) ∧
      (∀ R₁ R₂ : ℝ, 0 < R₁ → R₁ < R₂ → ∫ x in {x | R₁ < ‖x‖ ∧ ‖x‖ < R₂}, K x = 0) := by sorry

end DbarRegularity
