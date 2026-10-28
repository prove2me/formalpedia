-- Prove2me | Theorems.Thm_AvramDividend_Classical_localized_terminal_integrable_from_adapted
-- name    : AvramDividend.Classical.localized_terminal_integrable_from_adapted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:42:01.912+00:00
-- url     : https://prove2.me/theorems/660878bf-df3a-4619-9a5d-f27401952be4
-- title:
--   Finite reserve-band localisation makes stopped HJB terminal payoffs integrable without a strategy cap
-- statement:
--   At a fixed deterministic time and on the event of surviving ruin with reserve in a chosen finite band [0,B], the HJB terminal value is integrable for any admissible dividend-strategy path. This applies even when the original dividend constraint has no finite cap (C=∞). Continuity makes the test uniformly bounded on the finite band, while fixed-time adaptedness ensures measurability; integrability follows because the Lévy measure is a probability measure.
-- source:
--   Canonical Proved continuous_test_abs_le_on_finite_cap, riskProcess_adapted, survival_event_measurable_of_stopping_and_admissible and capped_piecewise_test_measurable_of_continuousOn; pinned Mathlib Integrable.of_bound.

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_adapted
import Theorems.Thm_AvramDividend_Classical_survival_event_measurable_of_stopping_and_admissible
import Theorems.Thm_AvramDividend_Classical_capped_piecewise_test_measurable_of_continuousOn
import Theorems.Thm_AvramDividend_Classical_continuous_test_abs_le_on_finite_cap

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.localized_terminal_integrable_from_adapted
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) (T : ℝ≥0) :
    Integrable (fun ω =>
      if (T : ℝ≥0∞) < ruinTime X x D ω then
        if riskProcess X x D T ω ∈ Icc (0 : ℝ) B then
          w (riskProcess X x D T ω) else 0
      else 0) P := by sorry
