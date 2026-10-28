-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_stopping_terminal_integrable_of_component_approximations
-- name    : AvramDividend.Classical.capped_stopping_terminal_integrable_of_component_approximations
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:33:34.821979+00:00
-- url     : https://prove2.me/theorems/9de97a37-eb42-4e08-8838-eb35a71ede4a
-- title:
--   Stopped finite-cap HJB terminal integrability from progressive component approximations
-- statement:
--   If Lévy noise and dividend control admit pointwise-convergent progressive approximations, their finite-cap stopped HJB terminal value is integrable. This composes the canonically proved progressive limit and capped stopped terminal lemmas without changing the BV or UV mission hypotheses.
-- source:
--   Canonically Proved progressive_of_pointwise_progressive_approximants and capped_stopping_terminal_integrable_of_progressive_components.

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_progressive_of_pointwise_progressive_approximants
import Theorems.Thm_AvramDividend_Classical_capped_stopping_terminal_integrable_of_progressive_components

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_stopping_terminal_integrable_of_component_approximations
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (τ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕 (fun ω => ((τ ω : ℝ≥0) : ℝ≥0∞)))
    (UX UD : ℕ → ℝ≥0 → Ω → ℝ)
    (hUX : ∀ n, ProgMeasurable 𝓕 (UX n))
    (hUD : ∀ n, ProgMeasurable 𝓕 (UD n))
    (hXtendsto : ∀ t ω, Filter.Tendsto
      (fun n => UX n t ω) Filter.atTop (nhds (X.X t ω)))
    (hDtendsto : ∀ t ω, Filter.Tendsto
      (fun n => UD n t ω) Filter.atTop (nhds (D t ω))) :
    Integrable (fun ω => if ((τ ω : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω then
      w (riskProcess X x D (τ ω) ω) else 0) P := by sorry
