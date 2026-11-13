-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
-- name    : AvramDividend.Classical.avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:10:10.410803+00:00
-- url     : https://prove2.me/theorems/e33982e1-3a7a-4182-8de3-cae5cd328508
-- title:
--   Original finite-negative-activity intrinsic Gaussian residual exists as adapted L1 martingale
-- statement:
--   Under the original spectrally negative Lévy Standing and finite negative-jump activity assumptions, the intrinsic Gaussian residual is constructed as a compact-uniform almost-sure limit of the true original cutoff residuals, is almost everywhere adapted to the original right-continuous filtration, globally integrable at every deterministic time, and has exact martingale conditional expectations.
-- source:
--   Avram Palmowski Pistorius (2007), Proposition 4(i), same-source Gaussian martingale driving the controlled Ito-Meyer calculation; original theorems 3a9ebf2b and 08823aa3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_mix_gauss14_original_intrinsic_limit_rightCont_ae_adapted
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin16_gaussian_residual_original_martingale_l1_public
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P,
        (∀ T : ℝ≥0,
          Tendsto
            (fun n : ℕ =>
              avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω)
            atTop (𝓝 (R T ω))) ∧
        (∀ K : ℕ, ∀ η : ℝ, 0 < η →
          ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
            ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
            |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
              R T ω| ≤ η)) ∧
      (∀ T : ℝ≥0,
        AEStronglyMeasurable[𝓕.rightCont T] (R T) P) ∧
      (∀ T : ℝ≥0, Integrable (R T) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (R t) ω = R s ω) := by sorry
