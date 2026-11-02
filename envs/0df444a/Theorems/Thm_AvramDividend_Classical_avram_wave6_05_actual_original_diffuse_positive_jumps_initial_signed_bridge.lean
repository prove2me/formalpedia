-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_original_diffuse_positive_jumps_initial_signed_bridge
-- name    : AvramDividend.Classical.avram_wave6_05_actual_original_diffuse_positive_jumps_initial_signed_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:01:48.905182+00:00
-- url     : https://prove2.me/theorems/7b4f89b0-4b37-42d8-ad6c-c52fdeef8f6b
-- title:
--   Actual original complete Stieltjes diffuse signed term plus chronological positive jumps and cap-linear initial payment
-- statement:
--   For an arbitrary actual IsAdmissibleLe dividend strategy, decompose the genuine original closed-horizon dividendMeasure, including its time-zero and terminal atoms, into the exact positive right-atomic component and atomless remainder. The discounted cash lintegral splits exactly, preserving all absolutely continuous and singular-continuous Stieltjes payments. Under the strict original source-prejump derivative bound almost everywhere with respect to the actual atomless remainder, the sum of its signed diffuse correction, any countable summable collection of actual positive pre-ruin right-jump corrections inside the horizon, and the actual time-zero cap-linear correction is nonpositive. The source-left Lévy jump is included in each riskProcess before the right dividend; no finite-jump, dividend smoothness, or artificial prepayment convention is imposed. The cap-linear initial term is essential when x exceeds a finite cap.
-- source:
--   Combine canonical actual-measure atomless split and discounted derivative sign with canonical countable positive-time w right-jump residual nonpositivity and the canonical all-time cap-linear V secant at time zero. Add three real nonpositive inequalities via linear arithmetic.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_dividend_full_measure_diffuse_strictpre_signed_bridge
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_original_positive_countable_w_right_payment_correction_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_wave6_05_actual_alltime_caplinear_dividend_jump_drop

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal BigOperators

theorem AvramDividend.Classical.avram_wave6_05_actual_original_diffuse_positive_jumps_initial_signed_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (q : ℝ) (w V : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (hVtop : C = ⊤ → ∀ y : ℝ, V y = w y)
    (hVfinite : C ≠ ⊤ → ∀ y : ℝ,
      V y = if y ≤ C.toReal then w y
        else w C.toReal + (y - C.toReal))
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D)
    (ω : Ω) (T : ℝ≥0)
    (B : Set ℝ≥0) (hBCount : B.Countable)
    (hB : ∀ t : B, 0 < (t : ℝ≥0) ∧
      ((t : ℝ≥0) : ℝ≥0∞) < ruinTime X x D ω)
    (hBWithin : ∀ t : B, (t : ℝ≥0) ≤ T)
    (hSummable : Summable (fun t : B =>
      Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (riskProcess X x D (t : ℝ≥0) ω -
            (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
          w (riskProcess X x D (t : ℝ≥0) ω)))) :
    let μ : Measure ℝ :=
      (dividendMeasure D ω).restrict (Icc (0 : ℝ) (T : ℝ))
    ∃ (A : Set ℝ) (μatom μdiffuse : Measure ℝ),
      A.Countable ∧ MeasurableSet A ∧
      μ = μatom + μdiffuse ∧
      μatom = Measure.sum (fun t : A => μ {(t : ℝ)} • Measure.dirac (t : ℝ)) ∧
      μatom Aᶜ = 0 ∧ NullSingletonClass μdiffuse ∧
      (∀ t : ℝ≥0, t ≤ T →
        μ {(t : ℝ)} =
          ENNReal.ofReal (rightLimit D t ω - D t ω)) ∧
      ((∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μ) =
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μatom) +
        (∫⁻ s, ENNReal.ofReal (Real.exp (-(q * s))) ∂μdiffuse)) ∧
      ((∀ᵐ s ∂μdiffuse.restrict
          (paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ)),
        1 ≤ deriv w (x +
          Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
          rightLimit D s.toNNReal ω)) →
        (∫ s in paymentTimes (ruinTime X x D ω) ∩ Icc (0 : ℝ) (T : ℝ),
          Real.exp (-(q * s)) *
            (1 - deriv w (x +
              Function.leftLim (fun r : ℝ≥0 => X.X r ω) s.toNNReal -
              rightLimit D s.toNNReal ω)) ∂μdiffuse) +
        (∑' t : B, Real.exp (-(q * ((t : ℝ≥0) : ℝ))) *
          ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
            w (riskProcess X x D (t : ℝ≥0) ω -
              (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)) -
            w (riskProcess X x D (t : ℝ≥0) ω))) +
        ((rightLimit D 0 ω - D 0 ω) +
          V (riskProcess X x D 0 ω -
            (rightLimit D 0 ω - D 0 ω)) -
          V (riskProcess X x D 0 ω)) ≤ 0) := by sorry
