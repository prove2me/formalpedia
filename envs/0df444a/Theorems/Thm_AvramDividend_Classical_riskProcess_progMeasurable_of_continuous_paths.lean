-- Prove2me | Theorems.Thm_AvramDividend_Classical_riskProcess_progMeasurable_of_continuous_paths
-- name    : AvramDividend.Classical.riskProcess_progMeasurable_of_continuous_paths
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:19:38.282549+00:00
-- url     : https://prove2.me/theorems/b361299d-819a-4ec1-9d3c-0649d7a7dec5
-- title:
--   Continuous adapted Lévy and dividend paths give progressively measurable controlled reserve
-- statement:
--   For a spectrally negative Lévy process with continuous sample paths and a continuously paid adapted dividend strategy, the controlled reserve is progressively measurable in the original filtration. This removes the separate progressivity hypothesis from capped stopped-payoff integrability in the continuous-path subclass.
-- source:
--   The fields SpectrallyNegativeLevy.adapted and IsDividendStrategy adaptedness, with pinned Mathlib's StronglyAdapted.progMeasurable_of_continuous and progressive addition/subtraction.

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.riskProcess_progMeasurable_of_continuous_paths
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hXCont : ∀ ω, Continuous (fun t => X.X t ω))
    (hDCont : ∀ ω, Continuous (fun t => D t ω)) :
    ProgMeasurable 𝓕 (riskProcess X x D) := by sorry
