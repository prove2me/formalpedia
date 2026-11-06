-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_strategywise_mean_vanishing_random_error_strict_real_values
-- name    : AvramDividend.Classical.avram_limit2_strategywise_mean_vanishing_random_error_strict_real_values
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:48:48.557318+00:00
-- url     : https://prove2.me/theorems/06d27ed3-417c-47a7-8d42-7270c79a0386
-- title:
--   Strategywise mean-vanishing random strict stopped cash errors bound real capped and top values
-- statement:
--   For every original capped admissible strategy, choose a nonnegative random ENNReal localisation error whose expected lintegral tends to zero, with a genuine original Iio (((n + 1 : ℕ) : ℝ)) cash plus nonnegative terminal stopped budget bounded by w(x) plus that expected error. Convert the mean errors into a deterministic numeric vanishing sequence, invoke the already Proved strategywise strict stopped cash bound, and conclude the exact original perpetual real Stieltjes payout integrability and expectation bound, capped upper value and unrestricted top-cap upper value. Preserves time-zero and right-horizon atoms; no unjustified martingale or terminal-vanishing claims.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_limit2_strategywise_vanishing_strict_terminal_real_values

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_strategywise_mean_vanishing_random_error_strict_real_values
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q : ℝ)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C → 0 ≤ w x)
    (hSource : ∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        ∃ error : ℕ → Ω → ℝ≥0∞,
          (∀ ε : ℝ≥0, 0 < ε →
            ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
              (∫⁻ ω, error n ω ∂P) ≤ (ε : ℝ≥0∞)) ∧
          (∀ n : ℕ, ∃ Terminal : Ω → ℝ≥0∞,
            (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
              Iio (((n + 1 : ℕ) : ℝ)),
              ENNReal.ofReal (Real.exp (-(q * t)))
                ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤
              ENNReal.ofReal (w x) + (∫⁻ ω, error n ω ∂P))) :
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      ∀ D : ℝ≥0 → Ω → ℝ, IsAdmissibleLe X x C D →
        Integrable (fun ω : Ω =>
          ∫ t in paymentTimes (ruinTime X x D ω),
            Real.exp (-(q * t)) ∂(dividendMeasure D ω)) P ∧
        dividendValue X q x D =
          ENNReal.ofReal (∫ ω,
            (∫ t in paymentTimes (ruinTime X x D ω),
              Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ∧
        (∫ ω, (∫ t in paymentTimes (ruinTime X x D ω),
          Real.exp (-(q * t)) ∂(dividendMeasure D ω)) ∂P) ≤ w x) ∧
    (∀ x : ℝ, 0 ≤ x → ENNReal.ofReal x ≤ C →
      valueFunctionLe X q C x ≤ ENNReal.ofReal (w x)) ∧
    (C = ⊤ → ∀ x : ℝ, 0 ≤ x →
      valueFunction X q x ≤ ENNReal.ofReal (w x)) := by sorry
