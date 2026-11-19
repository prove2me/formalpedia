-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_actual_three_tail_source_common_cutoff_epsilon
-- name    : AvramDividend.Classical.avram_pj_workerC_actual_three_tail_source_common_cutoff_epsilon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T00:38:52.014341+00:00
-- url     : https://prove2.me/theorems/f8c63678-692e-417c-88d9-91625815a978
-- title:
--   One original negative-mark cutoff jointly controls nonlinear Taylor absolute, squared and full generator errors
-- statement:
--   For the true left-limit controlled reserve, actual spectrally negative Lévy jump measure, finite predictable physical measure and deterministic bounded clock, select a single negative-mark tail index making the stopped nonlinear Taylor L1 energy, squared Taylor L2 energy and truncated full-generator drift L1 error each less than epsilon. The same cutoff index is used for all three source errors.
-- source:
--   Public Proved decd1b90 original nonlinear L1/L2 tail and 60413ba8 original finite-horizon negative generator truncation L1, combined by eventually_lt and common atTop index.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_actual_three_tail_source_common_cutoff_epsilon
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
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (T : ℝ≥0)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
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
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ ε : ℝ, 0 < ε →
      ∃ n : ℕ,
        (∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) <
            ENNReal.ofReal ε ∧
        (∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) <
            ENNReal.ofReal ε ∧
        (∫⁻ p : ℝ≥0 × Ω,
          ‖(∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) -
            (∫ z in Iio (0 : ℝ) \ B n, JG (p,z) ∂X.ν)‖ₑ
          ∂(((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) <
            ENNReal.ofReal ε := by sorry
