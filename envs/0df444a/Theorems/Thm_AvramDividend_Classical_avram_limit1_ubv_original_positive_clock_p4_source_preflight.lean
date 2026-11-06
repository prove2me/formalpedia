-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit1_ubv_original_positive_clock_p4_source_preflight
-- name    : AvramDividend.Classical.avram_limit1_ubv_original_positive_clock_p4_source_preflight
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:49:02.780228+00:00
-- url     : https://prove2.me/theorems/d29ca716-eb23-4ad9-9e74-b2bba9796608
-- title:
--   Original UBV positive-clock Ito source side conditions from exact stopping, cash and HJB certificates
-- statement:
--   For the genuine original spectrally negative Levy process at any positive reserve and capped admissible dividend strategy, discharge every deterministic and measurable source side condition of the P4-F source Ito-Meyer residual: the finite clipped ruin NNReal clock is exactly min(ruin,n), a right-continuous stopping time, measurable as real; the original piecewise W, closed Stieltjes Cash and discounted terminal Term are literally constructed, Term is a.e. strongly measurable and Cash integrable. The original nonlinear HJB maximum with UBV C2 smoothness supplies generator sign, gradient floor, candidate nonnegativity before ruin and every admissible right-payment jump secant including time zero. All these are composed from already Proved original-process theorems, with no equality-in-law, stochastic martingale residual, finite-window cash bound or terminal vanishing assumed. The P4 residual martingale identities remain unproved and outside this helper.

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

theorem AvramDividend.Classical.avram_limit1_ubv_original_positive_clock_p4_source_preflight
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_hjb : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧
        max (X.generator w y - q * w y) (1 - deriv w y) = 0)
    (x : ℝ) (hx : 0 < x) (hxc : ENNReal.ofReal x ≤ C)
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
