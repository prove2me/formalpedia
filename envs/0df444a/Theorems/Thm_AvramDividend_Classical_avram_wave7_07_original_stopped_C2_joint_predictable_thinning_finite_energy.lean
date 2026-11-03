-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy
-- name    : AvramDividend.Classical.avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:20:54.656907+00:00
-- url     : https://prove2.me/theorems/70cc5bb4-cef8-45f7-908d-fc10651207c6
-- title:
--   Finite L1 and L2 negative-mark energy under arbitrary predictable thinning of the original stopped C² source Taylor kernel
-- statement:
--   For the actual spectrally negative Lévy process X, original dividend strategy D, prepayment left-limit reserve, inclusive ruin stopping indicator, source Lévy measure X.ν, and C² Taylor compensation with truncation z in (-1,0), any jointly predictable time-state/negative-mark thinning set S preserves a predictable integrated drift and both finite negative-mark L1 and L2 source energy over each finite predictable clock μ. It strengthens the already-Proved joint predictability result using the already-Proved original stopped full-negative C2 L1/L2 theorem; it makes no assertion of a Poisson replacement process or an unproved intrinsic source jump compensator.
-- source:
--   Wave7 Chat07 original-source jump-compensation finite-energy thinning interface; direct consequence of Proved 0e0663b1 stopped full-negative C2 source L1/L2 and Proved 95e71e5b joint predictable mark thinning, intended for W7-06 and W7-08.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_stopped_C2_joint_predictable_mark_thinning_drift

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy
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
      (inferInstance : MeasurableSpace ℝ)] S) :
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
    Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ), (S.indicator HS) (p,z) ∂X.ν) ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal (|(S.indicator HS) (p,z)|) ∂X.ν ∂μ) < ⊤ ∧
    (∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((S.indicator HS (p,z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by sorry
