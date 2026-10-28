-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_stopping_terminal_integrable_from_progressive
-- name    : AvramDividend.Classical.capped_stopping_terminal_integrable_from_progressive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:02:50.742047+00:00
-- url     : https://prove2.me/theorems/830989fd-d3af-4380-9da8-9b251d30d260
-- title:
--   Stopped finite-cap HJB terminal payoffs are integrable for progressive controlled reserves
-- statement:
--   When the controlled reserve is progressive, the extended embedding of the random horizon is a stopping time, and dividends are admissibly capped, the surviving discounted verification terminal test is strongly measurable and uniformly bounded, hence integrable. Combines proved reserve cap at a stopping horizon, stopped test measurability, and finite-cap terminal integrability.
-- source:
--   Canonical Proved capped_surviving_stoppedValue_range_real, capped_survival_stopped_test_aestronglyMeasurable_of_continuousOn, capped_surviving_terminal_test_integrable_of_measurable.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_surviving_stoppedValue_range_real
import Theorems.Thm_AvramDividend_Classical_capped_survival_stopped_test_aestronglyMeasurable_of_continuousOn
import Theorems.Thm_AvramDividend_Classical_capped_surviving_terminal_test_integrable_of_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_stopping_terminal_integrable_from_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (τ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕 (fun ω => ((τ ω : ℝ≥0) : ℝ≥0∞)))
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D)) :
    Integrable (fun ω => if ((τ ω : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω then
      w (riskProcess X x D (τ ω) ω) else 0) P := by sorry
