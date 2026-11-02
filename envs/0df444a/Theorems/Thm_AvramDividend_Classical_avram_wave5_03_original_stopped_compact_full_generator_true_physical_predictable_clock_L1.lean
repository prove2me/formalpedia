-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_stopped_compact_full_generator_true_physical_predictable_clock_L1
-- name    : AvramDividend.Classical.avram_wave5_03_original_stopped_compact_full_generator_true_physical_predictable_clock_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:37:54.190232+00:00
-- url     : https://prove2.me/theorems/a6771154-c174-4952-8ad0-5c6ca0e7c511
-- title:
--   Actual finite original predictable physical clock and full compact ruin-stopped source generator-triplet L1
-- statement:
--   Stronger nonvacuous original-source counterpart of canonically Proved 648e8603: the exact true finite predictable clock agrees on EVERY predictable set with actual [0,T] Lebesgue time times original P, while the joint ruin-stopped compact C2 Gaussian curvature, c w'−q w and the genuine negative Lévy generator-integrand drift are Bochner L1 on THIS SAME clock. Reuses the same source 04-B clock and 03 Chat previous Proved component lemmas, with no artificial zero-measure witness or unproved stochastic Ito identity. This supplies the clock identity needed for exact HJB drift sign and compensated-martingale handoff to BV/UBV.
-- source:
--   Strict genuine-clock strengthening of canonical Proved 648e8603, using exact 04-B 16857b34 product equality and same original stopped Lévy/control component L1 theorems c254b492, d8eacc25, fbf81db0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_signed_jump_drift_L1_on_true_predictable_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_controlled_compact_gaussian_generator_drift_L1_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_controlled_compact_linear_generator_residual_L1_predictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_stopped_compact_full_generator_true_physical_predictable_clock_L1
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
    (q : ℝ) (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)
      else 0
    let L : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then X.c * deriv w (Y p) - q * w (Y p)
      else 0
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      ρ p.1 * (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable (fun p : ℝ≥0 × Ω =>
        (ρ p * G p + ρ p * L p) +
          (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν)) μ := by sorry
