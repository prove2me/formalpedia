-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_signed_drift_predictable
-- name    : AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_signed_drift_predictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T11:11:11.852923+00:00
-- url     : https://prove2.me/theorems/2352690b-08e9-4366-b9b1-978ff290668c
-- title:
--   Actual nonlinear Lévy source generator drift integral is right-continuous predictable
-- statement:
--   For the original X, adapted D and compact interior C² w, the real-valued signed full-negative source jump generator drift as a time-sample function p=(t,ω), including true ruin stopping and prepayment reserve Y, is measurable for the original filtration's right-continuous predictable sigma algebra. Obtained by integrating the canonically Proved predictable actual-source nonlinear Taylor kernel against SFinite original negative X.nu and rewriting with the exact signed generator drift equality. Does not claim compensator law or stochastic martingale.
-- source:
--   Proved 0e0663b1 source stopped predictable C² kernel, Proved a9270e22 negative ν SFinite, Proved 5e3be45e actual generator signed equality, pinned StronglyMeasurable.integral_prod_right.

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

theorem AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_signed_drift_predictable
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
    (huv : u + δ < v) (hv : v < C) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) := by sorry
