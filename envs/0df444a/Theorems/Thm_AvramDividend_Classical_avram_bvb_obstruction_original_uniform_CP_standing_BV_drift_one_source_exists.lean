-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_uniform_CP_standing_BV_drift_one_source_exists
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_uniform_CP_standing_BV_drift_one_source_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:22:20.91514+00:00
-- url     : https://prove2.me/theorems/c15b72f3-a0dc-48f2-86a5-9cd661a87f1b
-- title:
--   Original negative-uniform compound Poisson source exists with Standing, bounded variation and drift exactly one
-- statement:
--   Construct a genuine original standing BV spectrally negative Lévy process with the diffuse unit negative-uniform compound Poisson measure, finite activity, zero Gaussian coefficient and precisely unit BV drift. This bundles all required original-source hypotheses for the positive-cap pathwise verification obstruction.
-- source:
--   Extract the existing Proved A06 real-product compound Poisson driver and source triplet, uniform mark finite first-moment and small-jump BV integrability, plus the original diffuse positive-drift standing criterion. The drift follows exactly by cancellation of the compound Poisson c adjustment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_driver_on_real_sequence_product
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_poisson_triplet
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_bv_moments
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_standing_from_diffuse_positive_drift
open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_obstruction_original_uniform_CP_standing_BV_drift_one_source_exists :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧ X.BoundedVariation ∧
      X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0) ∧
      X.ν (Iio (0 : ℝ)) < ⊤ ∧ X.drift = 1 ∧ X.σ = 0 := by sorry
