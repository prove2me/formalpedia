-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_comp8_original_X_integrable_any_clock
-- name    : AvramDividend.Classical.avram_p3_comp8_original_X_integrable_any_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T18:45:52.606174+00:00
-- url     : https://prove2.me/theorems/7e6dcf49-3edc-4e09-aae4-0cc6986c2d30
-- title:
--   Original finite-first-moment bounded-variation Lévy path is integrable at every finite time
-- statement:
--   For the original X under Standing and bounded variation, the fixed-time Lévy position X.X(t) is integrable at every finite t. Prove integer clocks by stationary Lévy increment additivity from integrable X.X(1), then dominate the nonnegative BV residual at arbitrary t by that at an integer horizon.
-- source:
--   Derived from Proved unit-integrability and all-time monotone BV residual plus Proved stationary-increment X integrability addition. Needed to remove artificial T≤1 restriction in BV-ERROR7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_X_integrable_mean_additivity
import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_residual_ae_monotone_all_times
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_comp8_original_X_integrable_any_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (t : ℝ≥0) :
    Integrable (X.X t) P := by sorry
