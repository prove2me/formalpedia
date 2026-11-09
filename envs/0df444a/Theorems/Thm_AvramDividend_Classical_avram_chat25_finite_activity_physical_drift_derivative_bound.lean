-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat25_finite_activity_physical_drift_derivative_bound
-- name    : AvramDividend.Classical.avram_chat25_finite_activity_physical_drift_derivative_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T16:45:03.315365+00:00
-- url     : https://prove2.me/theorems/fa9b7e98-e889-42d9-9743-870696cb7e0e
-- title:
--   Finite-jump BV HJB upper bound controls derivative by value and jump intensity
-- statement:
--   For the original BV spectrally negative Levy generator with finite negative jump intensity and globally nonnegative candidate, HJB superharmonicity bounds physical drift times candidate derivative above by discount plus jump rate times candidate value. This is a finite-activity source bound needed to control the positive-horizon stopped-grid process in 233260f7.
-- source:
--   Finite-activity branch of b0dd41fe: source-exact generator identity c8ba98f0, integrable increments 5ff8b9b4, Mathlib integral_mono_ae, finite constant integrability.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_boundedVariation_generator_physical_drift_representation
import Theorems.Thm_AvramDividend_Classical_boundedVariation_full_negative_jump_increment_integrable
open MeasureTheory Set Filter
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_chat25_finite_activity_physical_drift_derivative_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (w : ℝ → ℝ) (hw_nonneg : ∀ z, 0 ≤ w z)
    (q y : ℝ) (hGen : X.GeneratorIntegrable w y)
    (hHJB : X.generator w y - q * w y ≤ 0) :
    X.drift * deriv w y ≤
      (q + (X.ν (Iio (0 : ℝ))).toReal) * w y := by sorry
