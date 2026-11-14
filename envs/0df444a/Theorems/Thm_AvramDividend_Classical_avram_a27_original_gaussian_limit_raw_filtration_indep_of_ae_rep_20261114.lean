-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_gaussian_limit_raw_filtration_indep_of_ae_rep_20261114
-- name    : AvramDividend.Classical.avram_a27_original_gaussian_limit_raw_filtration_indep_of_ae_rep_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:38:55.427194+00:00
-- url     : https://prove2.me/theorems/7a6bb5da-b694-46a5-8ca2-ea82aed19841
-- title:
--   Original Gaussian intrinsic limit has raw-source-filtration independent increments for any almost-everywhere equivalent global representative
-- statement:
--   Any globally defined original source Gaussian residual limit representative agreeing almost everywhere simultaneously at all times has increments independent of the uncompleted original filtration at each earlier time.
-- source:
--   Proved A24 original future-path past-independent representative 9e32027d and A27 sigma-algebra AE independence transfer.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_uniform_gaussian_limit_original_past_independent_rep_20261113
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Any all-time source-a.e. representative of the original Gaussian limit has original raw-filtration independent increments. -/

theorem AvramDividend.Classical.avram_a27_original_gaussian_limit_raw_filtration_indep_of_ae_rep_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R G : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ u : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n u ω)
        atTop (𝓝 (R u ω)))
    (hEq : ∀ᵐ ω ∂P, ∀ u : ℝ≥0, G u ω = R u ω) :
    ∀ s t : ℝ≥0, s ≤ t →
      Indep (MeasurableSpace.comap (fun ω => G t ω - G s ω) inferInstance)
        (𝓕 s) P := by sorry
