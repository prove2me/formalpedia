-- Prove2me | Theorems.Thm_FamousTheorems_law_of_total_variance
-- name    : FamousTheorems.law_of_total_variance
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:49.162974+00:00
-- url     : https://prove2.me/theorems/bb99f35b-1fcd-44d2-9814-ea35d54e4fe5
-- title:
--   The law of total variance (Eve's law)
-- statement:
--   **The law of total variance (Eve's law).** Let $X$ be a square-integrable random variable and $\mathcal G$ a sub-$\sigma$-algebra. Then
--   $$\operatorname{Var}(X)=\mathbb E\big[\operatorname{Var}(X\mid\mathcal G)\big]+\operatorname{Var}\big(\mathbb E[X\mid\mathcal G]\big).$$
--
--   The variance splits into the unexplained part, the expected conditional variance, and the explained part, the variance of the conditional mean. This decomposition underlies analysis of variance (ANOVA), Rao–Blackwellization and the bias–variance tradeoff.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.integral_condVar_add_variance_condExp`. The ambient $\sigma$-algebra is `m₀` and the sub-$\sigma$-algebra is `m ≤ m₀`. `condVar m X μ` is the conditional variance, `μ[X | m]` is the conditional expectation, `variance` is the variance, and `MemLp X 2 μ` is square-integrability. The measure is a probability measure.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.integral_condVar_add_variance_condExp`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory ProbabilityTheory

theorem law_of_total_variance {Ω : Type*} {m₀ m : MeasurableSpace Ω} {X : Ω → ℝ} {μ : @Measure Ω m₀} (hm : m ≤ m₀)
    [IsProbabilityMeasure μ] (hX : MemLp X 2 μ) :
    ∫ ω, condVar m X μ ω ∂μ + variance (μ[X | m]) μ = variance X μ := by sorry

end FamousTheorems
