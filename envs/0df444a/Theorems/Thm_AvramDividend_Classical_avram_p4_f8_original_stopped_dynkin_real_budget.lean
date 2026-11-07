-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f8_original_stopped_dynkin_real_budget
-- name    : AvramDividend.Classical.avram_p4_f8_original_stopped_dynkin_real_budget
-- status  : Open
-- author  : @WillR
-- created : 2026-11-06T12:37:10.113014+00:00
-- url     : https://prove2.me/theorems/91b6bf73-8a10-48a0-a57e-ccc57dc7b7ae
-- title:
--   Finite original Gaussian-jump stopped Dynkin real-valued supermartingale budget
-- statement:
--   For the actual non-BV spectrally negative Levy process with nonzero Gaussian and jump parts, a top-cap C2 q-HJB supersolution stopped on the three-way bounded corrected exit clock has an integrable real discounted terminal potential and its expected value is at most w(1). This is the substantive stochastic Itô/Dynkin localisation and compensated-martingale obligation, independent of ENNReal conversion.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f8_original_stopped_dynkin_real_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν ≠ 0) (hσ : X.σ ≠ 0)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hTop : C = ⊤) :
    ∀ (b : ℝ) (n : ℕ), 1 ≤ b →
      let τ : Ω → ℝ≥0∞ := fun ω =>
        min (twoSidedExitUpTimeCorrected X (b - 1) ω)
          (min (twoSidedExitDownTimeCorrected X (-1) ω) (n : ℝ≥0∞))
      Integrable (fun ω => Real.exp (-(q * ENNReal.toReal (τ ω))) *
        w (1 + X.X (ENNReal.toNNReal (τ ω)) ω)) P ∧
      (∫ ω, Real.exp (-(q * ENNReal.toReal (τ ω))) *
        w (1 + X.X (ENNReal.toNNReal (τ ω)) ω) ∂P) ≤ w 1 := by sorry
