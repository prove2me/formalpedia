-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
-- name    : AvramDividend.Classical.avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:47:25.102205+00:00
-- url     : https://prove2.me/theorems/f36bf9b5-c984-4a85-b386-a11b9fa149f9
-- title:
--   Every finite negative-jump cutoff is square integrable on the original space
-- statement:
--   If the original spectrally negative Levy process has finite negative jump activity, each original small-band compensated cutoff at a fixed physical time has integrable square. Deduce this from the existing uniform original-process L2 envelope and the source's adapted measurability. This supplies the jump-square clause of the original Gaussian finite-cutoff moment certificate.
-- source:
--   J-A21 from Proved c64684fd and 7ba6e5dc; no auxiliary Brownian construction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja21_original_finite_activity_smallband_cutoff_square_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (t : ℝ≥0) :
    Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_small_band_compensated X n t ω) ^ 2) P := by sorry
