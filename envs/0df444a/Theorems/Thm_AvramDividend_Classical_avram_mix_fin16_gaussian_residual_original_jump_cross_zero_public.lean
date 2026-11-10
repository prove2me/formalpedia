-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin16_gaussian_residual_original_jump_cross_zero_public
-- name    : AvramDividend.Classical.avram_mix_fin16_gaussian_residual_original_jump_cross_zero_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-09T13:08:26.755186+00:00
-- url     : https://prove2.me/theorems/6a16a86c-440e-4760-a733-bffc3fe8ebf1
-- title:
--   Original intrinsic Gaussian increment is orthogonal to complementary jump increment
-- statement:
--   Prove the integrable zero cross moment of the genuine original Gaussian increment with the complementary jump/drift increment, including possible finite-activity large negative marks under Standing integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin16_gaussian_residual_original_jump_cross_zero_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto
        (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω)))
    (hRadapt : ∀ t : ℝ≥0,
      AEStronglyMeasurable[𝓕.rightCont t] (R t) P) :
    ∀ s t : ℝ≥0, s ≤ t →
      let cross : Ω → ℝ := fun ω =>
        (R t ω - R s ω) *
          ((X.X t ω - X.X s ω) - (R t ω - R s ω))
      Integrable cross P ∧ (∫ ω, cross ω ∂P) = 0 := by sorry
