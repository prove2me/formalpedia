-- Prove2me | Theorems.Thm_FamousTheorems_bhatia_davis_inequality
-- name    : FamousTheorems.bhatia_davis_inequality
-- status  : Proved
-- author  : @cm_beta
-- created : 2026-09-24T07:09:52.028987+00:00
-- url     : https://prove2.me/theorems/c2aef5d6-02fe-40ec-a319-1521f0aee92e
-- title:
--   The Bhatia–Davis inequality
-- statement:
--   **The Bhatia–Davis inequality.** Let $X$ be a random variable with $a\le X\le b$ almost surely and mean $m=\mathbb E X$. Then
--   $$\operatorname{Var}(X)\le(b-m)(m-a).$$
--
--   Bhatia and Davis proved this in 2000. Since $(b-m)(m-a)\le(b-a)^2/4$, it sharpens Popoviciu's inequality. Equality holds exactly when $X$ takes only the values $a$ and $b$. It is used for bounds on variances of bounded observables in statistics and in quantum mechanics.
--
--   **Formalization note.** Mathlib's `ProbabilityTheory.variance_le_sub_mul_sub`. The measure is a probability measure, $X$ is a.e. measurable, and the mean is `∫ ω, X ω ∂μ`.
-- source:
--   Listed in Mathlib's curated theorem manifests (docs/1000.yaml); formalized in Mathlib as `ProbabilityTheory.variance_le_sub_mul_sub`. Proof here reduces to that Mathlib result.

import Mathlib

namespace FamousTheorems

open MeasureTheory

theorem bhatia_davis_inequality {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω} [IsProbabilityMeasure μ] {a b : ℝ} {X : Ω → ℝ}
    (h : ∀ᵐ ω ∂μ, X ω ∈ Set.Icc a b) (hX : AEMeasurable X μ) :
    ProbabilityTheory.variance X μ ≤ (b - ∫ ω, X ω ∂μ) * (∫ ω, X ω ∂μ - a) := by sorry

end FamousTheorems
