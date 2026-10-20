-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_restrict_Ioc_measurable
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_restrict_Ioc_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T23:06:45.598085+00:00
-- url     : https://prove2.me/theorems/d763694e-e35d-43bf-90d6-3d1a42a067ed
-- title:
--   Random running-supremum Stieltjes measure restricted to a fixed interval is measurable
-- statement:
--   For every spectrally negative Lévy process and any fixed real half-open interval (l,u], the actual dividend Stieltjes measure of its running-supremum regulator, restricted to that interval, is a measurable random measure as a function of the sample point. Apply the existing general theorem for dividend-strategy Stieltjes measures to the running supremum after establishing that the running supremum itself satisfies IsDividendStrategy. This provides a direct input to the measurable-integral construction needed to justify stochastic interval reward measurability and exchange of countable rewards and expectations.
-- source:
--   Dependency-gated runningSup_isDividendStrategy authoring request d918c202-327a-4faf-b5da-336efb9de3b5; proved dividendMeasure_restrict_Ioc_measurable target 6895c621-3aaf-4437-a604-4b9274673dae.

import Theorems.Thm_AvramDividend_Classical_runningSup_isDividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_restrict_Ioc_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_restrict_Ioc_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (l u : ℝ) :
    Measurable (fun ω : Ω =>
      (dividendMeasure (runningSup X) ω).restrict (Set.Ioc l u)) := by sorry
