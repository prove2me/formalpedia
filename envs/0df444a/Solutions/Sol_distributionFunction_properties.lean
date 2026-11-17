-- Prove2me | solution 1 for distributionFunction_properties
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T21:14:44.433992+00:00
-- url     : https://prove2.me/submissions/910ad31e-55c9-4234-a3d8-08dd29c2b3e2

import Definitions.Def_ProbabilityTheory_chapter_03_def_3_4_F000
import Mathlib.Probability.CDF


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter
open MeasureTheory ProbabilityTheory

open scoped ENNReal Topology


theorem solution (P : Measure ℝ) [IsProbabilityMeasure P] :
    Monotone (distributionFunction P) ∧
    (∀ x, ContinuousWithinAt (distributionFunction P) (Ici x) x) ∧
    Tendsto (distributionFunction P) atTop (𝓝 1) ∧
    Tendsto (distributionFunction P) atBot (𝓝 0) := by
  -- We prove that our distributionFunction is equivalent to the standard Mathlib cdf.
  have h_eq : distributionFunction P = cdf P := by
    ext x
    rw [distributionFunction, ← ofReal_cdf P x]
    -- Since cdf P x is the underlying function of a StieltjesFunction, it is always finite.
    -- cdf_nonneg ensures the value is non-negative, allowing ENNReal.toReal_ofReal to simplify.
    exact ENNReal.toReal_ofReal (cdf_nonneg P x)

  -- Use the properties provided by the cdf API.
  rw [h_eq]
  refine ⟨(cdf P).mono, (cdf P).right_continuous, tendsto_cdf_atTop P, tendsto_cdf_atBot P⟩