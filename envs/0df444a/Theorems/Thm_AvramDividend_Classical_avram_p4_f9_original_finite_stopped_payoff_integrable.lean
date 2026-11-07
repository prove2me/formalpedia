-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f9_original_finite_stopped_payoff_integrable
-- name    : AvramDividend.Classical.avram_p4_f9_original_finite_stopped_payoff_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:44:16.694022+00:00
-- url     : https://prove2.me/theorems/4e42cb37-7e76-4166-a6c2-0e15ea2cfcba
-- title:
--   Original mixed-Levy finite stopped discounted HJB payoff is integrable
-- statement:
--   Establish the original process finite three-way stopped terminal payoff's measurability and integrability, using corrected stopping-time measurability, adaptation and the bounded upper envelope w(b). This independent step supplies a legitimate integrable real terminal payoff for the stopped Dynkin argument.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_TwoSidedExitCorrected
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f9_original_finite_stopped_payoff_integrable
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
      Integrable (fun ω => Real.exp (-(q * ENNReal.toReal (τ ω))) * w (1 + X.X (ENNReal.toNNReal (τ ω)) ω)) P := by sorry
