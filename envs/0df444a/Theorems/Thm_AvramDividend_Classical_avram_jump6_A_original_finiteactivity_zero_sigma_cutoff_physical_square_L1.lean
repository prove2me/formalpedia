-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_finiteactivity_zero_sigma_cutoff_physical_square_L1
-- name    : AvramDividend.Classical.avram_jump6_A_original_finiteactivity_zero_sigma_cutoff_physical_square_L1
-- status  : Open
-- author  : @WillR
-- created : 2026-11-22T21:16:25.702832+00:00
-- url     : https://prove2.me/theorems/117c124c-22d1-474c-bbd3-3c2a1475d00a
-- title:
--   Original finite-activity zero-Gaussian cut-off residual has finite second moment from physical jump-count L2
-- statement:
--   For a finite-activity original spectrally negative Levy source with σ=0, the original zero-truncation residual has integrable square at every finite clock T. Derive physically: the Gaussian residual limit vanishes almost surely, the source cutoff-to-limit bound is controlled by the actual all-negative jump count and the finite intensity compensator, and that physical jump count has an L2 moment. This is a genuine original-source case of c7a69857, without a Gaussian companion construction.
-- source:
--   Original source target c7a69857; Proved a21 sigma-zero residual limit 77f47f2e, mix_fin13 limit existence 0d7f9ed2, anoise20 residual count inequality fae860dd, anoise18 physical count L2 a6562a4d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_finiteactivity_zero_sigma_cutoff_physical_square_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSigma : X.σ = 0) (T : ℝ≥0) :
    Integrable (fun ω =>
      (avram_p4_h_gaussian_intrinsic_truncated_residual X 0 T ω) ^ 2) P := by sorry
