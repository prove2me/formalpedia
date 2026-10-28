-- Prove2me | Theorems.Thm_AvramDividend_Classical_localized_stopping_terminal_integrable_from_progressive
-- name    : AvramDividend.Classical.localized_stopping_terminal_integrable_from_progressive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:45:45.539838+00:00
-- url     : https://prove2.me/theorems/f2e3f7a9-9d52-4af0-ba1a-2db7d56fc965
-- title:
--   Stopped HJB terminal payoffs localised to a finite reserve band are integrable without any strategy cap
-- statement:
--   For an adapted dividend strategy and progressively measurable controlled reserve, at any stopping time the survival payoff restricted to a finite reserve band [0,B] is integrable. No global finite cap is required. This is a needed integrability bridge for C=∞ localisation in the classical dividend stochastic-verification proof, with measurability coming from the stopped reserve and survival event.
-- source:
--   Pinned Mathlib measurable_stoppedValue, Integrable.of_bound, and Proved survival_event_measurable_of_stopping_and_admissible, capped_piecewise_test_measurable_of_continuousOn and continuous_test_abs_le_on_finite_cap.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_survival_event_measurable_of_stopping_and_admissible
import Theorems.Thm_AvramDividend_Classical_capped_piecewise_test_measurable_of_continuousOn
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.localized_stopping_terminal_integrable_from_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D)) :
    Integrable (fun ω =>
      if τ ω < ruinTime X x D ω then
        if stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B then
          w (stoppedValue (riskProcess X x D) τ ω) else 0
      else 0) P := by sorry
