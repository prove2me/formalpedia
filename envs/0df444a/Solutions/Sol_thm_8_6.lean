-- Prove2me | solution 1 for thm_8_6
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T23:35:03.24192+00:00
-- url     : https://prove2.me/submissions/c220d12f-447e-45e9-9296-39489c215548

import Definitions.Def_ProbabilityTheory_chapter_08_thm_8_6_support
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open TVCore
noncomputable section

/-- Exported wrapper for Theorem 8.6 containing both the discrete and continuous formulas. -/
theorem solution :
    (∀ (P Q : Measure ℕ) (_ : IsProbabilityMeasure P) (_ : IsProbabilityMeasure Q),
      totalVariationDistance P Q = (1 / 2 : ℝ) * ∑' n, |P.real {n} - Q.real {n}|) ∧
    (∀ (f g : ℝ → ℝ),
      Measurable f →
      Measurable g →
      Integrable f volume →
      Integrable g volume →
      (∀ x, 0 ≤ f x) →
      (∀ x, 0 ≤ g x) →
      (∫ x, f x = 1) →
      (∫ x, g x = 1) →
      totalVariationDistance (densityMeasure f) (densityMeasure g)
        = (1 / 2 : ℝ) * ∫ x, |densityDiff f g x|) := by
  constructor
  · intro P Q hP hQ
    letI := hP
    letI := hQ
    exact thm_8_6_discrete P Q
  · intro f g hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob
    exact thm_8_6_continuous hf_meas hg_meas hf_int hg_int hf_nonneg hg_nonneg hf_prob hg_prob
