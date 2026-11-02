-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_true_clock_compact_generator_hjb_L1_nonpositive
-- name    : AvramDividend.Classical.avram_wave5_03_original_true_clock_compact_generator_hjb_L1_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T15:51:21.02324+00:00
-- url     : https://prove2.me/theorems/1829a383-5bb4-4a8c-88f9-4fe035565617
-- title:
--   The actual stopped source Lévy generator HJB residual is integrable and nonpositive on the exact finite physical predictable clock
-- statement:
--   On the actual spectrally negative Lévy X and adapted original-control prepayment reserve, with inclusive true ruin indicator and compact positive interior band, construct the finite predictable physical-time clock μ equal to the actual horizon-restricted Lebesgue time×P measure on every predictable set, and show that the full original source generator-minus-q drift is Bochner integrable and has nonpositive integrated expectation whenever the genuine HJB generator inequality holds in the band. The proof identifies the original Gaussian, c w'−q w and negative jump generator-remainder via canonical source triplet equality, then uses the full true-clock L1 theorem and pointwise original HJB. It does not assert a conditional Ito identity or drop zero boundary for downstream BV/UBV.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), actual stopped HJB generator drift; extends 04B source clock 16857b34, Chat03 c254/d8e/fbf and new verified exact generator triplet/true-clock.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_compact_stopped_triplet_equals_full_generator
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_stopped_compact_full_generator_true_physical_predictable_clock_L1
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03_original_true_clock_compact_generator_hjb_L1_nonpositive
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
    (q : ℝ) (T : ℝ≥0)
    (hw_gen : ∀ y : ℝ, 0 < y → y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let R : ℝ≥0 × Ω → ℝ := fun p =>
      ρ p * (if Y p ∈ Icc (u + δ) v then
        X.generator w (Y p) - q * w (Y p) else 0)
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable R μ ∧
      (∫ p, R p ∂μ) ≤ 0 := by sorry
