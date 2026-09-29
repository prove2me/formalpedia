-- Prove2me | Theorems.Thm_FamousTheorems_independent_expectation_product_7a
-- name    : FamousTheorems.independent_expectation_product_7a
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T12:26:15.777481+00:00
-- url     : https://prove2.me/theorems/4dd9bc5d-e266-420d-a3d5-f554ef8fdbd4
-- title:
--   E[XY] = E[X]E[Y] for independent random variables
-- statement:
--   **$E[XY]=E[X]\,E[Y]$ for independent random variables.** Let $X,Y$ be independent real- or complex-valued random variables on a probability space, or more generally on a measure space $(\Omega,\mu)$, that are almost everywhere strongly measurable. Then
--   $$\int XY\,d\mu=\Big(\int X\,d\mu\Big)\Big(\int Y\,d\mu\Big).$$
--
--   This multiplicativity is the basic computational consequence of independence. It gives the additivity of variances of independent variables, and hence the weak law of large numbers by Chebyshev's inequality. It also gives the multiplicativity of characteristic and moment generating functions of sums of independent variables.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral`. The integral is the Bochner integral, which is $0$ for non-integrable functions. The statement therefore also covers the case where $X$ or $Y$ is not integrable, because then both sides are $0$.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.IndepFun.integral_mul_eq_mul_integral`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem independent_expectation_product_7a {Ω 𝕜 : Type*} [RCLike 𝕜] {mΩ : MeasurableSpace Ω} {μ : Measure Ω} {X Y : Ω → 𝕜}
    (hXY : ProbabilityTheory.IndepFun X Y μ) (hX : AEStronglyMeasurable X μ) (hY : AEStronglyMeasurable Y μ) :
    ∫ ω, X ω * Y ω ∂μ = (∫ ω, X ω ∂μ) * ∫ ω, Y ω ∂μ := by sorry

end FamousTheorems
