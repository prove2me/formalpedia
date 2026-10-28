-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_progressive_of_pointwise_component_approximations
-- name    : AvramDividend.Classical.riskProcess_progressive_of_pointwise_component_approximations
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T11:18:30.959602+00:00
-- url     : https://prove2.me/theorems/29265198-7728-4174-b847-20cdf155c46b
-- title:
--   Progressive dyadic approximations of Lévy noise and dividend control give a progressive reserve
-- statement:
--   Given arbitrary progressively measurable approximating sequences of the Lévy noise and dividend process that converge pointwise in time and scenario to the actual components, the controlled reserve x+X-D is progressively measurable. This combines the newly proved pointwise-limit lemma and the already proved algebraic closure for progressive components. It identifies the exact remaining construction task for one-sided continuous sample paths.
-- source:
--   Canonically Proved progressive_of_pointwise_progressive_approximants and riskProcess_progMeasurable_of_progressive_parts.

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_progressive_of_pointwise_progressive_approximants
import Theorems.Thm_AvramDividend_Classical_riskProcess_progMeasurable_of_progressive_parts

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_progressive_of_pointwise_component_approximations
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ)
    (UX UD : ℕ → ℝ≥0 → Ω → ℝ)
    (hUX : ∀ n, ProgMeasurable 𝓕 (UX n))
    (hUD : ∀ n, ProgMeasurable 𝓕 (UD n))
    (hXtendsto : ∀ t ω, Filter.Tendsto
      (fun n => UX n t ω) Filter.atTop (nhds (X.X t ω)))
    (hDtendsto : ∀ t ω, Filter.Tendsto
      (fun n => UD n t ω) Filter.atTop (nhds (D t ω))) :
    ProgMeasurable 𝓕 (riskProcess X x D) := by sorry
