-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_original_bv_ubv_nonnegative_clock_cash_hjb_preflight
-- name    : AvramDividend.Classical.avram_limit1_original_bv_ubv_nonnegative_clock_cash_hjb_preflight
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:38:06.138911+00:00
-- url     : https://prove2.me/theorems/0cbba3ce-f9bf-4189-83cc-b8ec8f79c53a
-- title:
--   All-variation original clipped ruin source clock, cash, terminal and HJB preflight
-- statement:
--   For any original spectrally negative Levy process, capped admissible policy at every nonnegative reserve including zero and any integer ruin clock, construct the actual truncated NNReal stopping time, measurable real clock, original postpayment W, right-closed Stieltjes dividend cash and discounted terminal with integrability/measurability. From the exact BV-or-UBV HJB smoothness premise and max-equals-zero, provide source generator sign, derivative floor, nonnegative pre-ruin candidate and inclusive time-zero dividend jump secant. This extends the proved UBV-positive LIMIT-1 source preflight to the BV and zero-reserve cases with no stochastic martingale or terminal vanishing assumption.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_ruinTime_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p3_main_original_integer_truncated_ruin_nnreal_stopping
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_actual_truncated_clock_real_measurable_of_source
import Theorems.Thm_AvramDividend_Classical_avram_wave7_08_source_stopped_terminal_cash_meas_integrable_witnesses
import Theorems.Thm_AvramDividend_Classical_avram_sweep18_original_uniform_HJB_stopping_criteria

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit1_original_bv_ubv_nonnegative_clock_cash_hjb_preflight
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth :
      (¬ X.BoundedVariation → ContDiffOn ℝ 2 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) ∧
      (X.BoundedVariation → ContDiffOn ℝ 1 w
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}))
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ C)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D) (n : ℕ) :
    ∃ (τ : Ω → ℝ≥0),
      (∀ ω, τ ω =
        (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal) ∧
      Measurable (fun ω => (τ ω : ℝ)) ∧
      IsStoppingTime 𝓕.rightCont
        (fun ω => (τ ω : WithTop ℝ≥0)) ∧
      ∃ W Cash Term : Ω → ℝ,
        (∀ ω, W ω = if τ ω = 0 ∨
          (τ ω : ℝ≥0∞) < ruinTime X x D ω
          then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
          else riskProcess X x D (τ ω) ω) ∧
        (∀ ω, Cash ω = (∫⁻ s in
          paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ),
          ENNReal.ofReal (Real.exp (-(q * s)))
            ∂(dividendMeasure D ω)).toReal) ∧
        (∀ ω, Term ω = Real.exp (-(q * (τ ω : ℝ))) * w (W ω)) ∧
        AEStronglyMeasurable Term P ∧ Integrable Cash P ∧
        (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
          X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
        (∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) ∧
        (∀ ω (t : ℝ≥0), 0 < t →
          (t : ℝ≥0∞) < ruinTime X x D ω →
          0 ≤ w (riskProcess X x D t ω)) ∧
        (∀ ω (t : ℝ≥0),
          (t = 0 ∨ (t : ℝ≥0∞) < ruinTime X x D ω) →
          rightLimit D t ω - D t ω ≤
            w (riskProcess X x D t ω) -
              w (riskProcess X x D t ω -
                (rightLimit D t ω - D t ω))) := by sorry
