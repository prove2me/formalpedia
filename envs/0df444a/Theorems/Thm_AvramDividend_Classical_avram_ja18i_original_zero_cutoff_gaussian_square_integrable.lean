-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18i_original_zero_cutoff_gaussian_square_integrable
-- name    : AvramDividend.Classical.avram_ja18i_original_zero_cutoff_gaussian_square_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T09:00:44.032597+00:00
-- url     : https://prove2.me/theorems/1b4a4a54-af3f-4101-88f8-d50ed706eeaa
-- title:
--   Original zero-cutoff Gaussian residual has finite quadratic moment under finite negative jump activity
-- statement:
--   For the original spectrally negative Lévy process on its given probability space, assume Standing and finite negative-jump intensity. Show the physical intrinsic Gaussian residual at cutoff n=0, with large-jump marks cancelled and small marks compensated in the original process, has an integrable square at each deterministic horizon. Large negative-jump second moments are not assumed.
-- source:
--   AVRAM J-A18 finite-cutoff variance base L2 reduction from original process

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18i_original_zero_cutoff_gaussian_square_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∀ (t : ℝ≥0), Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω) ^ 2) P := by sorry
