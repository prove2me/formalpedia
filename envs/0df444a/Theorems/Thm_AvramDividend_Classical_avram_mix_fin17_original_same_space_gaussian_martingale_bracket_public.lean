-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin17_original_same_space_gaussian_martingale_bracket_public
-- name    : AvramDividend.Classical.avram_mix_fin17_original_same_space_gaussian_martingale_bracket_public
-- status  : Open
-- author  : @WillR
-- created : 2026-11-09T13:34:22.362197+00:00
-- url     : https://prove2.me/theorems/261ec08d-fd80-462b-b41f-677e1f65fe70
-- title:
--   Original intrinsic Gaussian residual martingale and sigma-square without large-mark moment assumptions
-- statement:
--   On the original finite-activity Levy sample space and unchanged right-continuous filtration, the exact source Gaussian truncation limit is adapted, integrable, a martingale, and has second moment equal to time times Gaussian variance. No cross product with raw large negative marks is required, since finite intensity need not imply integrable negative jump size.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin17_original_same_space_gaussian_martingale_bracket_public
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ R : ℝ≥0 → Ω → ℝ,
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        Tendsto
          (fun k : ℕ =>
            avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
          atTop (nhds (R t ω))) ∧
      (∀ t : ℝ≥0,
        AEStronglyMeasurable[𝓕.rightCont t] (R t) P) ∧
      (∀ t : ℝ≥0, Integrable (R t) P) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (R t) ω = R s ω) ∧
      (∀ t : ℝ≥0,
        Integrable (fun ω => (R t ω) ^ 2) P ∧
        (∫ ω, (R t ω) ^ 2 ∂P) = (t : ℝ) * X.σ ^ 2) := by sorry
