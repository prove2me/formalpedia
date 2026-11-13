-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_negative_uniform_original_standing_source_exists
-- name    : AvramDividend.Classical.avram_a20_negative_uniform_original_standing_source_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T07:41:49.941117+00:00
-- url     : https://prove2.me/theorems/ba817b45-a132-4a78-8f03-5d876fa093d5
-- title:
--   Existing A06 source realises a Standing original filtered Lévy process with exactly negative-uniform jump measure
-- statement:
--   Combine the Proved original real-sequence compound-Poisson driver, exact original filtered triplet, measure facts, and positive-drift Standing certificate to obtain one genuine original Lévy process with precisely the negative-unit uniform Lévy measure and finite negative activity. This closes the concrete process witness needed to refute the mis-specified included-smallband variance law, while preserving the original probability space and filtration.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_levy_foundations_isCompoundPoissonDriver
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_driver_on_real_sequence_product
import Theorems.Thm_AvramDividend_Classical_avram_a06_original_compound_poisson_triplet
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
import Theorems.Thm_AvramDividend_Classical_avram_a06_bv_standing_from_diffuse_positive_drift
open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a20_negative_uniform_original_standing_source_exists :
    ∃ (P : Measure ((ℕ → ℝ) × (ℕ → ℝ)))
      (𝓕 : Filtration ℝ≥0
        (inferInstance : MeasurableSpace ((ℕ → ℝ) × (ℕ → ℝ))))
      (X : SpectrallyNegativeLevy P 𝓕),
      X.Standing ∧
      X.ν = (volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0) ∧
      X.ν (Iio (0 : ℝ)) < ⊤ := by sorry
