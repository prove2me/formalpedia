-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_run1750_original_rightcont_full_cutoff_predictable_cell_orthogonal_past
-- name    : AvramDividend.Classical.avram_p4_s3_run1750_original_rightcont_full_cutoff_predictable_cell_orthogonal_past
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:14:49.603286+00:00
-- url     : https://prove2.me/theorems/c0a0f8a0-4977-4e48-bca0-7f24419d7324
-- title:
--   Genuine original predictable compensated negative-jump physical cell is L2-orthogonal to every earlier right-continuously adapted variable
-- statement:
--   For the real original spectrally negative Levy source X, a square-integrable past right-continuously adapted random variable F and bounded predictable coefficient H, the expected product of F and the actual physical future negative-cutoff compensated jump count H(N-r) is exactly zero. Both count L2 and conditional centring are proved original-source facts, not assumptions.
-- source:
--   Proved physical full cutoff bounded predictable conditional martingale step 2aaf4594, same-path original source right-continuous filtration lift e58a099d, accepted raw conditional orthogonality; no equality-in-law surrogate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_h_original_full_cutoff_bounded_weight_conditional_martingale_step
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_raw_conditional_cross_zero
open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_run1750_original_rightcont_full_cutoff_predictable_cell_orthogonal_past
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (s T : ℝ≥0) (cut : ℕ)
    (F : Ω → ℝ)
    (hF : StronglyMeasurable[𝓕.rightCont s] F)
    (hFL2 : MemLp F 2 P)
    (H : Ω → ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (L : ℝ) (hBound : ∀ ω, |H ω| ≤ L) :
    let N : Ω → ℝ≥0∞ := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ Iic (-(1 / ((cut : ℝ) + 1))))
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((cut : ℝ) + 1))))).toReal
    (∫ ω, F ω * (H ω * ((N ω).toReal - r)) ∂P) = 0 := by sorry
