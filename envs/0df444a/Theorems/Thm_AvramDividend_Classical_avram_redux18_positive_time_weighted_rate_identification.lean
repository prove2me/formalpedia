-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_redux18_positive_time_weighted_rate_identification
-- name    : AvramDividend.Classical.avram_redux18_positive_time_weighted_rate_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:08:45.116106+00:00
-- url     : https://prove2.me/theorems/03d8df06-2066-41e4-aa3b-bfdbb99f15a7
-- title:
--   Positive finite time scaling identifies intrinsic weighted negative-band Lévy rates
-- statement:
--   At any strictly positive finite horizon t, if the expected intrinsic and Lévy negative-band count measures have identical time-scaled values on every Borel subset of B, the intrinsic and Lévy weighted mark integrals agree on B. This is the exact bridge from source Proved original rate identities at arbitrary positive physical times to the weighted 1-exp(mark) Lévy compensator without assuming a canonical marked Poisson process.
-- source:
--   ENNReal.mul_left_inj cancels a positive non-top time scale in the setwise count-rate identity; Measure.ext identifies restricted measures; equality of their restricted lintegrals follows for arbitrary nonnegative weights.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_redux18_positive_time_weighted_rate_identification
    (t : ℝ≥0∞) (ht0 : t ≠ 0) (htTop : t ≠ ⊤)
    (μ ν : Measure ℝ) (B : Set ℝ) (hB : MeasurableSet B)
    (hCounts : ∀ C : Set ℝ, MeasurableSet C → C ⊆ B →
      t * μ C = t * ν C) (g : ℝ → ℝ≥0∞) :
    (∫⁻ y in B, g y ∂μ) = (∫⁻ y in B, g y ∂ν) := by sorry
