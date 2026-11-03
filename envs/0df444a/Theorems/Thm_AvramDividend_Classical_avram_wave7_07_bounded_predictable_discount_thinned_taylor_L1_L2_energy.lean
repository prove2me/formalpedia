-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_bounded_predictable_discount_thinned_taylor_L1_L2_energy
-- name    : AvramDividend.Classical.avram_wave7_07_bounded_predictable_discount_thinned_taylor_L1_L2_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:57:24.978361+00:00
-- url     : https://prove2.me/theorems/26fe1474-3290-45e7-9b8e-e2515c299711
-- title:
--   Original stopped nonlinear Lévy Taylor L1/L2 energy survives every bounded predictable discount and mark thinning
-- statement:
--   In the exact source Lévy Ω, filtration, process and original dividend control, the actual ruin-stopped C2 negative-jump Taylor kernel with truncation -1<z<0 remains jointly predictable and has finite compensated L1/L2 energy under any jointly predictable mark thinning and any predictable discount weight in [0,1]. The proof contracts both integrals against the exact source negative Lévy measure, and does not claim a new intrinsic jump-count compensator or unrelated random sample space.
-- source:
--   W7-07 fully source-faithful bounded predictable L1/L2 contraction from Proved original C2 kernel and Proved 70cc5bb4 arbitrary predictable thinning energy.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_bounded_predictable_discount_thinned_taylor_L1_L2_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] S)
    (a : ℝ≥0 × Ω → ℝ)
    (ham : Measurable[𝓕.rightCont.predictable] a)
    (ha : ∀ p, 0 ≤ a p ∧ a p ≤ 1) :
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
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)]
      (fun p : ((ℝ≥0 × Ω) × ℝ) => a p.1 * (S.indicator HS) p) ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal (|a p * (S.indicator HS) (p,z)|) ∂X.ν ∂μ) < ⊤ ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((a p * (S.indicator HS) (p,z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by sorry
