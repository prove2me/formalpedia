-- Prove2me | Theorems.Thm_AvramDividend_Classical_localized_stopped_terminal_expected_le_of_uniform_bands
-- name    : AvramDividend.Classical.localized_stopped_terminal_expected_le_of_uniform_bands
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:49:51.623363+00:00
-- url     : https://prove2.me/theorems/e7b18954-651a-4f39-8ec7-c6a0825de7dd
-- title:
--   Uniform stopped reserve-band terminal expectations imply the full expected HJB terminal bound
-- statement:
--   At the actual stopped Lévy reserve and measurable survival event, any common bound on the expected nonnegative HJB terminal payoff truncated to each finite reserve band bounds the unrestricted stopped terminal expectation. It is the domain-specific recovery interface for infinite-cap localisation.
-- source:
--   Canonically Proved localized_stopped_terminal_lintegral_iSup_bands (when available), followed by iSup_le.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_localized_stopped_terminal_lintegral_iSup_bands

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.localized_stopped_terminal_expected_le_of_uniform_bands
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D))
    (K : ℝ≥0∞)
    (hBound : ∀ n : ℕ,
      (∫⁻ ω, if τ ω < ruinTime X x D ω ∧
        0 ≤ stoppedValue (riskProcess X x D) τ ω ∧
        stoppedValue (riskProcess X x D) τ ω ≤ (n : ℝ) then
          ENNReal.ofReal (w (stoppedValue (riskProcess X x D) τ ω))
        else 0 ∂P) ≤ K) :
    (∫⁻ ω, if τ ω < ruinTime X x D ω ∧
      0 ≤ stoppedValue (riskProcess X x D) τ ω then
        ENNReal.ofReal (w (stoppedValue (riskProcess X x D) τ ω))
      else 0 ∂P) ≤ K := by sorry
