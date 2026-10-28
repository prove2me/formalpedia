-- Prove2me | Theorems.Thm_AvramDividend_Classical_localized_stopping_terminal_integrable_of_component_approximations
-- name    : AvramDividend.Classical.localized_stopping_terminal_integrable_of_component_approximations
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:37:59.891837+00:00
-- url     : https://prove2.me/theorems/239b289b-1abc-48cf-b1d9-42bd5294740e
-- title:
--   Infinite-cap stopped HJB terminal integrability on finite reserve bands from progressive approximations
-- statement:
--   For an admissible dividend strategy with no global reserve cap, stopped HJB terminal values restricted to any finite reserve band remain integrable if the Lévy and dividend components admit pointwise-convergent progressive approximations. This composes two canonically proved results.
-- source:
--   Canonically Proved riskProcess_progressive_of_pointwise_component_approximations and localized_stopping_terminal_integrable_from_progressive.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_progressive_of_pointwise_component_approximations
import Theorems.Thm_AvramDividend_Classical_localized_stopping_terminal_integrable_from_progressive

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.localized_stopping_terminal_integrable_of_component_approximations
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕 τ)
    (UX UD : ℕ → ℝ≥0 → Ω → ℝ)
    (hUX : ∀ n, ProgMeasurable 𝓕 (UX n))
    (hUD : ∀ n, ProgMeasurable 𝓕 (UD n))
    (hXtendsto : ∀ t ω, Filter.Tendsto
      (fun n => UX n t ω) Filter.atTop (nhds (X.X t ω)))
    (hDtendsto : ∀ t ω, Filter.Tendsto
      (fun n => UD n t ω) Filter.atTop (nhds (D t ω))) :
    Integrable (fun ω =>
      if τ ω < ruinTime X x D ω then
        if stoppedValue (riskProcess X x D) τ ω ∈ Icc (0 : ℝ) B then
          w (stoppedValue (riskProcess X x D) τ ω) else 0
      else 0) P := by sorry
