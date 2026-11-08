-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_ito_jumps13_original_random_clock_Taylor_kernel_predictable
-- name    : AvramDividend.Classical.avram_ubv_ito_jumps13_original_random_clock_Taylor_kernel_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T15:19:32.675763+00:00
-- url     : https://prove2.me/theorems/9a5b631b-4339-4cc5-adbd-9af5a3a7b694
-- title:
--   Original capped C2 random-clock stopped Taylor Lévy kernel is jointly predictable and mark measurable
-- statement:
--   For the original spectrally negative Levy process and dividend strategy, the actual discounted and inclusively ruin/random-clock stopped compact-band Taylor kernel is measurable on the original right-continuous predictable sigma algebra times Borel negative-mark space. Uses exact original predictable band, deterministic horizon and stopping masks and true stopped nonlinear Taylor measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_original_zero_negative_measurable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_inclusive_stopped_discounted_truncated_compensation_taylor_joint_predictable_mark_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_controlled_prestate_compact_band_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02c_deterministic_horizon_mask_rightcont_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-! Exact original source predictability of the compact stopped Taylor mark kernel. -/

theorem AvramDividend.Classical.avram_ubv_ito_jumps13_original_random_clock_Taylor_kernel_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (q : ℝ) (T : ℝ≥0) (σ : Ω → ℝ≥0)
    (hσ : IsStoppingTime 𝓕.rightCont (fun ω => (σ ω : WithTop ℝ≥0))) :
    let a : (ℝ≥0 × Ω) → ℝ := fun p =>
      if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
    let GW : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => a p.1 * HS p
    let GWσ : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1.1 ≤ σ p.1.2 then GW p else 0
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] GWσ := by sorry
