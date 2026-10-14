-- Prove2me | Theorems.Thm_DbarRegularity_integral_dbar_mul_inv_sq_eq
-- name    : DbarRegularity.integral_dbar_mul_inv_sq_eq
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T20:40:38.327915+00:00
-- url     : https://prove2.me/theorems/7e759721-7fa1-469c-aa4e-9504a3dcda5b
-- title:
--   Truncated integrals of the Cauchy-Riemann derivative against 1/z^2 as circle averages
-- statement:
--   Identify $y=(y_0,y_1)\in\mathbb R^2$ with $y_0+iy_1\in\mathbb C$. Let $f:\mathbb R^2\to\mathbb C$ be of class $C^1$ with compact support, and write $\bar\partial f=\partial f/\partial x_1+i\,\partial f/\partial x_2$. Then for every $x\in\mathbb R^2$ and every $\varepsilon>0$
--   $$\int_{|y|\ge\varepsilon}\frac{\bar\partial f(x-y)}{(y_0+iy_1)^2}\,dy=\frac1\varepsilon\int_{S^1}\frac{f(x-\varepsilon\omega)}{\omega_0+i\omega_1}\,d\sigma(\omega),$$
--   where $\sigma$ is the surface measure on the unit circle.
--
--   This expresses the truncated singular integrals with kernel $1/z^2$ applied to $\bar\partial f$ as averages of $f$ over small circles around $x$.
--
--   **Formalization Note.** $\mathbb R^2$ is `EuclideanSpace ℝ (Fin 2)`; $\partial f/\partial x_j(z)$ is `fderiv ℝ f z (EuclideanSpace.single j 1)` with `j = 0, 1`; the kernel is written `1 / ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ^ 2`; the left side is a Bochner set integral over `{y | ε ≤ ‖y‖}` with integrand `∂̄f(x - y) * K y`; the circle is the subtype `sphere 0 1` with `volume.toSphere`, and $1/\varepsilon$ is the real number `ε⁻¹` coerced to `ℂ`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter III, § 1.3, Proposition 4, p. 60

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar
import Mathlib.Analysis.Calculus.Deriv.ZPow
import Mathlib.Analysis.Calculus.FDeriv.Mul

namespace DbarRegularity

open MeasureTheory Metric Set

/-- For `f ∈ C¹_c(ℝ²)`, `x ∈ ℝ²` and `ε > 0`, the integral of
`(∂₁f + i ∂₂f)(x - y) / (y₀ + i y₁)²` over `|y| ≥ ε` equals
`ε⁻¹ ∫_{S¹} f(x - ε ω) / (ω₀ + i ω₁) dσ(ω)`. -/
theorem integral_dbar_mul_inv_sq_eq (f : EuclideanSpace ℝ (Fin 2) → ℂ) (hf : ContDiff ℝ 1 f)
    (hfc : HasCompactSupport f) (x : EuclideanSpace ℝ (Fin 2)) (ε : ℝ) (hε : 0 < ε) :
    ∫ y in {y : EuclideanSpace ℝ (Fin 2) | ε ≤ ‖y‖},
        (fderiv ℝ f (x - y) (EuclideanSpace.single 0 1) +
          Complex.I * fderiv ℝ f (x - y) (EuclideanSpace.single 1 1)) *
        (1 / ((y 0 : ℂ) + (y 1 : ℂ) * Complex.I) ^ 2) =
      ((ε⁻¹ : ℝ) : ℂ) * ∫ ω : sphere (0 : EuclideanSpace ℝ (Fin 2)) 1,
        f (x - ε • ω.1) / ((ω.1 0 : ℂ) + (ω.1 1 : ℂ) * Complex.I) ∂volume.toSphere := by sorry

end DbarRegularity
