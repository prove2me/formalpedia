-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_C2_joint_predictable_thinned_drift_integrable
-- name    : AvramDividend.Classical.avram_wave7_07_original_C2_joint_predictable_thinned_drift_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:31:39.275202+00:00
-- url     : https://prove2.me/theorems/3230b607-237a-4d9e-861e-13005fac3f8d
-- title:
--   Original stopped C² negative-jump Taylor drift is Bochner integrable after jointly predictable mark thinning
-- statement:
--   For the exact original source spectrally negative Lévy process X, its filtration and Lévy measure X.ν, the original dividend strategy D and ruin stop, any jointly predictable time-state/negative-mark thinning S preserves predictability and Bochner integrability of the negative source Taylor compensator drift over any finite predictable clock μ. The truncated kernel subtracts z times the derivative exactly when -1<z<0, and this is an integrability input for the original stopped Itô–Meyer expectation equation, not an assertion of the still-unproved intrinsic jump-count compensator.
-- source:
--   W7-07 new L1-to-Bochner drift bridge using Proved original stopped full negative C2 L1/L2 (0e0663b1), Proved predictable thinning (95e71e5b), and Proved negative Lévy measure sFinite (a9270e22).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_stopped_C2_joint_predictable_mark_thinning_drift
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_C2_joint_predictable_thinned_drift_integrable
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
    Integrable (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ), (S.indicator HS) (p,z) ∂X.ν) μ := by sorry
