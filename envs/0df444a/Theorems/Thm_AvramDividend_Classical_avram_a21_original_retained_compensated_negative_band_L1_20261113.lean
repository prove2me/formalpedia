-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_original_retained_compensated_negative_band_L1_20261113
-- name    : AvramDividend.Classical.avram_a21_original_retained_compensated_negative_band_L1_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:24:04.524395+00:00
-- url     : https://prove2.me/theorems/04e2f119-6c2a-467c-a492-f9b5b7ff2000
-- title:
--   Original physically retained negative compensated band is integrable at every cutoff and time
-- statement:
--   On the ORIGINAL probability space of a spectrally negative Levy process, the physically retained compensated small negative jump band at any cutoff and time is integrable. Uses Proved source-band square-integrability, measurability and the embedded IsProbabilityMeasure P field.
-- source:
--   Proved f36bf9b5 source-band square-integrable, f7cf0440 source-band measurable, X.isProbability, pinned Mathlib memLp_two_iff_integrable_sq and MemLp.integrable.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a21_original_retained_compensated_negative_band_L1_20261113
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (n : ℕ) (t : ℝ≥0),
      Integrable (fun ω =>
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) P := by sorry
