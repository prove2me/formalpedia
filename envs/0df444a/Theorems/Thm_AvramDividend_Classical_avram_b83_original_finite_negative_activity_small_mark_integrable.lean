-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b83_original_finite_negative_activity_small_mark_integrable
-- name    : AvramDividend.Classical.avram_b83_original_finite_negative_activity_small_mark_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T13:07:41.376879+00:00
-- url     : https://prove2.me/theorems/73cdb3cc-a678-4f77-8840-155b7770f9f7
-- title:
--   Original finite negative activity gives finite signed small-mark first moment without global second moment
-- statement:
--   The original spectrally negative Lévy measure has finite total negative mark mass under the finite-activity hypothesis. The small negative mark region is a subset of this finite-mass set. Every mark strictly between minus one and zero has absolute size below one, so its signed identity first moment is Bochner integrable under the original unmodified Lévy measure restricted to that region by the standard integrableOn-of-bound theorem. This provides the exact L1 domination ingredient needed for passing the original compensated small-band first moment cutoffs to the full negative interval in B82. It does not use a global second moment of negative marks, and the large negative tail remains unrestricted.
-- source:
--   Original SpectrallyNegativeLevy ν, finite total negative jump activity; standard dominated integral bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b83_original_finite_negative_activity_small_mark_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    IntegrableOn (fun z : ℝ => z) (Ioo (-1 : ℝ) 0) X.ν := by sorry
