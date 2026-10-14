-- Prove2me | Theorems.Thm_DbarRegularity_aestronglyMeasurable_integral_mul_sub
-- name    : DbarRegularity.aestronglyMeasurable_integral_mul_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T15:02:29.244037+00:00
-- url     : https://prove2.me/theorems/0d54859b-3015-4df5-bd54-3f1a7b17050c
-- title:
--   The pointwise convolution integral $x\mapsto\int K(x-y)f(y)\,dy$ is a.e. strongly measurable
-- statement:
--   Let $d\ge0$ and let $K,f:\mathbb R^d\to\mathbb C$ be almost-everywhere strongly measurable. Then the function
--   $$x\;\longmapsto\;\int_{\mathbb R^d}K(x-y)\,f(y)\,dy$$
--   is almost-everywhere strongly measurable on $\mathbb R^d$.
--
--   No integrability is assumed: at points $x$ where $y\mapsto K(x-y)f(y)$ is not integrable the Bochner integral is $0$ by convention, and the statement still holds. This is the basic measurability fact for convolution operators $f\mapsto K*f$ defined pointwise by the integral.
--
--   **Formalization Note.** $\mathbb R^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume`; the integral is the Bochner integral `∫ y, K (x - y) * f y`, which Lean sets to $0$ when the integrand is not integrable.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton University Press (1970), Chapter II, § 2.2, p. 29

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2

namespace DbarRegularity

open MeasureTheory
open scoped ENNReal

/-- The convolution-type integral `x ↦ ∫ K(x - y) f(y) dy` of a.e.-strongly measurable functions
is a.e.-strongly measurable. -/
theorem aestronglyMeasurable_integral_mul_sub {d : ℕ} (K f : EuclideanSpace ℝ (Fin d) → ℂ)
    (hK : AEStronglyMeasurable K volume) (hf : AEStronglyMeasurable f volume) :
    AEStronglyMeasurable (fun x => ∫ y, K (x - y) * f y) volume := by sorry

end DbarRegularity
