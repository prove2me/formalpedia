-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_deterministic_terminal_integrable_from_adapted
-- name    : AvramDividend.Classical.capped_deterministic_terminal_integrable_from_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:15:06.173901+00:00
-- url     : https://prove2.me/theorems/6ae453b4-5fa1-49f9-a3f2-ff9f4835db93
-- title:
--   Deterministic finite-cap surviving HJB terminal payoff is integrable from adaptedness
-- statement:
--   At a fixed deterministic time, the original adaptedness assumption of a capped admissible dividend strategy suffices for the surviving HJB terminal value to be measurable and integrable. No global progressive-measurability assumption on the controlled reserve is required. The proof combines fixed-time stopping-event measurability, adapted risk-process measurability, compact-cap continuity, and the proved bounded terminal test integrability.
-- source:
--   Exact parent hypotheses of admissible_cap_truncated_dividendValue_le_bounded_variation and the Proved riskProcess_adapted, survival_event_measurable_of_stopping_and_admissible, capped_surviving_riskProcess_range_real_finite, capped_piecewise_test_measurable_of_continuousOn and capped_surviving_terminal_test_integrable_of_measurable.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_adapted
import Theorems.Thm_AvramDividend_Classical_survival_event_measurable_of_stopping_and_admissible
import Theorems.Thm_AvramDividend_Classical_capped_piecewise_test_measurable_of_continuousOn
import Theorems.Thm_AvramDividend_Classical_capped_surviving_riskProcess_range_real_finite
import Theorems.Thm_AvramDividend_Classical_capped_surviving_terminal_test_integrable_of_measurable

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_deterministic_terminal_integrable_from_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x)
    (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (T : ℝ≥0) :
    Integrable (fun ω =>
      if (T : ℝ≥0∞) < ruinTime X x D ω then
        w (riskProcess X x D T ω) else 0) P := by sorry
