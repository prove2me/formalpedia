-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_discounted_stopped_full_generator_triplet_true_clock_L1
-- name    : AvramDividend.Classical.avram_wave5_03_original_discounted_stopped_full_generator_triplet_true_clock_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:50:36.711518+00:00
-- url     : https://prove2.me/theorems/eaf85167-dd4d-448d-9520-6085f82029d8
-- title:
--   Discounted true original physical predictable clock integrates all three stopped Lévy generator drift components
-- statement:
--   On the literal original SpectrallyNegativeLevy X, same admissible control D, true inclusive ruin stop and compact C2 generator band, the actual [0,T] Lebesgue-time×P predictable clock integrates the entire discounted exp(-q t) source Lévy triplet residual. This includes Gaussian σ²w''/2, linear c w'−qw and signed full negative generatorIntegrand ν drift without path copies. The clock agrees on all original predictable measurable sets with source physical product P. The theorem uses Proved true-clock L1 a6771154 and proves deterministic exp(-qt) is genuinely strongly predictable for the original right-continuous filtration and bounded by 1 for q≥0; bounded multiplication yields Bochner L1. It does not assume stochastic Ito or a compensated martingale.
-- source:
--   Avram–Palmowski–Pistorius (2007) Proposition 4(i); Proved actual product-clock full unweighted generator L1 a6771154 and strongly adapted left-continuous predictable theorem 5ae104c4.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_stopped_compact_full_generator_true_physical_predictable_clock_L1
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_strongAdapted_leftContinuous_predictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_discounted_stopped_full_generator_triplet_true_clock_L1
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
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) :
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
        Real.exp (-(q * (p.1 : ℝ))) *
          ((ρ p * G p + ρ p * L p) +
            (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν))) μ := by sorry
