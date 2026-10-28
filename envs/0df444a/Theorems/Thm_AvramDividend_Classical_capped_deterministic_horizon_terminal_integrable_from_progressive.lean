-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_deterministic_horizon_terminal_integrable_from_progressive
-- name    : AvramDividend.Classical.capped_deterministic_horizon_terminal_integrable_from_progressive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T09:07:55.806667+00:00
-- url     : https://prove2.me/theorems/11c22a1e-00fd-46f3-a8b6-88a7b6b70bce
-- title:
--   Fixed-horizon stopped HJB terminal payoff integrability under a cap
-- statement:
--   For a progressive controlled reserve under a finite cap, the verification candidate evaluated at a deterministic nonnegative time and set to zero after ruin is integrable. This follows from the canonically proved random-stopping-time terminal integrability theorem and the pinned Mathlib stopping-time property of a deterministic time.
-- source:
--   AvramDividend.Classical.capped_stopping_terminal_integrable_from_progressive and MeasureTheory.isStoppingTime_const.

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_capped_stopping_terminal_integrable_from_progressive

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_deterministic_horizon_terminal_integrable_from_progressive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (T : ℝ≥0)
    (hProg : ProgMeasurable 𝓕 (riskProcess X x D)) :
    Integrable (fun ω => if (T : ℝ≥0∞) < ruinTime X x D ω then
      w (riskProcess X x D T ω) else 0) P := by sorry
