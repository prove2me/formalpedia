-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_stopped_compact_full_generator_three_drift_components_L1
-- name    : AvramDividend.Classical.avram_wave5_03_original_stopped_compact_full_generator_three_drift_components_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:20:39.923307+00:00
-- url     : https://prove2.me/theorems/648e8603-d230-4b8c-bff5-54b667235ce9
-- title:
--   Original finite-horizon predictable clock integrates the full ruin-stopped local Gaussian, linear and nonlinear jump-generator drift components
-- statement:
--   On the exact original spectrally negative Lévy path and same adapted dividend control, the finite physical-time predictable measure furnished by Proved 04-B 16857b34 simultaneously integrates the stopped compact C² Gaussian drift σ²w''/2, the linear c w' minus discounted value q w and the true full negative Lévy nonlinear generator jump drift. The survival mask is the actual inclusive ruinTime stopping mask, proved right-continuous predictable. No global smoothness of w, surrogate Poisson process, Brownian copy, missing boundary premise or assumed stochastic Itô formula is used. This discharges the three deterministic first-moment drift component obligations in the controlled Itô–Meyer generator decomposition for corrected UBV 429e17ca; the stochastic martingale chain identity remains separate.
-- source:
--   Canonical Proved 04-B 16857b34; Chat03 source jump c254b492; source Gaussian d8eacc25 and linear fbf81db0 (must be verified Proved before publication); source true ruin predictability 658fb6a1/69806d16.

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

theorem AvramDividend.Classical.avram_wave5_03_original_stopped_compact_full_generator_three_drift_components_L1
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
      Integrable (fun p : ℝ≥0 × Ω =>
        (ρ p * G p + ρ p * L p) +
          (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν)) μ := by sorry
