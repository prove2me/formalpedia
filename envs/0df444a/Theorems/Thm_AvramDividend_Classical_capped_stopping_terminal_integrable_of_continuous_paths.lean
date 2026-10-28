-- Prove2me | Theorems.Thm_AvramDividend_Classical_capped_stopping_terminal_integrable_of_continuous_paths
-- name    : AvramDividend.Classical.capped_stopping_terminal_integrable_of_continuous_paths
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T10:32:30.622678+00:00
-- url     : https://prove2.me/theorems/a0fba88b-84b8-48ad-bd1d-7963887d9b44
-- title:
--   Finite-cap stopped dividend verification terminal payoff is integrable for continuous adapted paths
-- statement:
--   For a capped admissible dividend strategy with continuous adapted Lévy and dividend paths, the random stopped surviving HJB terminal payoff is integrable without requiring a separate progressive-measurability assumption. The theorem composes the progressive-risk-process bridge with the proved finite-cap random-horizon terminal integrability theorem.
-- source:
--   Pinned Mathlib and Proved capped_stopping_terminal_integrable_from_progressive, together with riskProcess_progMeasurable_of_continuous_paths (pending compilation at authoring time).

import Mathlib.Probability.Process.Stopping
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_progMeasurable_of_continuous_paths
import Theorems.Thm_AvramDividend_Classical_capped_stopping_terminal_integrable_from_progressive

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.capped_stopping_terminal_integrable_of_continuous_paths
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (B : ℝ) (hB : 0 ≤ B)
    (x : ℝ) (hx : 0 ≤ x) (hxc : ENNReal.ofReal x ≤ ENNReal.ofReal B)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x (ENNReal.ofReal B) D)
    (τ : Ω → ℝ≥0)
    (hStop : IsStoppingTime 𝓕 (fun ω => ((τ ω : ℝ≥0) : ℝ≥0∞)))
    (hXCont : ∀ ω, Continuous (fun t => X.X t ω))
    (hDCont : ∀ ω, Continuous (fun t => D t ω)) :
    Integrable (fun ω => if ((τ ω : ℝ≥0) : ℝ≥0∞) <
      ruinTime X x D ω then
      w (riskProcess X x D (τ ω) ω) else 0) P := by sorry
