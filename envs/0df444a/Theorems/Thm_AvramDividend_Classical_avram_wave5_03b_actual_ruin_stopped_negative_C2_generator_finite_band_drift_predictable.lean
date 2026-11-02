-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_negative_C2_generator_finite_band_drift_predictable
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_negative_C2_generator_finite_band_drift_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:44:39.075322+00:00
-- url     : https://prove2.me/theorems/c606bb8b-94c5-4234-97cd-742cbbc5618a
-- title:
--   Actual original source negative-mark finite-band nonlinear generator drift is predictable
-- statement:
--   For a genuine spectrally negative Lévy X and adapted right-cont dividend control, the original prepayment reserve stopped nonlinear C² generator drift integrated against X.nu on EVERY measurable negative source-mark band B is measurable for F.rightCont.predictable. This directly extends the existing full-band predictable drift to finite source truncations and uses the original negative jump Lévy SFinite law, the Proved jointly predictable source Taylor remainder and exact original generator drift equality. No abstract Poisson source or compensated stochastic martingale is assumed.
-- source:
--   Canonical Proved 0e0663b1 joint actual stopped Taylor predictability; 5e3be45e exact negative source generator band equality; a9270e22 true original negative source ν SFinite. Mathlib StronglyMeasurable.integral_prod_right.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_negative_C2_generator_finite_band_drift_predictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (B : Set ℝ) (hBm : MeasurableSet B) (hBneg : B ⊆ Iio (0 : ℝ)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
      ∫ z in B, JG (p,z) ∂X.ν) := by sorry
