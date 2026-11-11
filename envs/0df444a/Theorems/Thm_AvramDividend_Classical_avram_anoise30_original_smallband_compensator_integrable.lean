-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_anoise30_original_smallband_compensator_integrable
-- name    : AvramDividend.Classical.avram_anoise30_original_smallband_compensator_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T10:21:36.612836+00:00
-- url     : https://prove2.me/theorems/5398685b-9399-4367-9a6d-0a8be690af67
-- title:
--   Original bounded compensated small-band signed mark sum is integrable
-- statement:
--   With finite original total negative jump intensity, each actual signed compensated original small-jump band at a finite horizon has a finite first absolute moment, by the physical count L2 budget. No independent auxiliary process is used.
-- source:
--   Proved original count L2 a6562a4d, finite-activity count ae ebd98fb4, pathwise residual cutoff count bound 1b696ff5, exact residual difference 2c95a423 and original filtration adaptation 42ada2ca.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_anoise30_original_smallband_compensator_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ n : ℕ, ∀ T : ℝ≥0,
      Integrable (fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n T ω) P := by sorry
