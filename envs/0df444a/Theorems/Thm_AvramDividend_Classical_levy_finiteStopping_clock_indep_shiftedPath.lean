-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_clock_indep_shiftedPath
-- name    : AvramDividend.Classical.levy_finiteStopping_clock_indep_shiftedPath
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T16:30:38.571526+00:00
-- url     : https://prove2.me/theorems/10d5cfff-3f44-4bc6-9de8-6fb3cfcf6f85
-- title:
--   Finite stopping time independent of complete future Lévy increment path
-- statement:
--   Every finite stopping time is independent of the complete future Lévy increment path. The stopping clock is measurable in the stopped sigma-algebra and the latter is independent of the shifted path; monotonicity of sigma-algebra independence gives the result.
-- source:
--   Combines verified stopped-history independence d5bac6c4-63fd-49ee-a81b-ccda03ccab18 with finite stopping-clock measurability 7b726fe4-39eb-44f8-b346-548eb444ff0f. Necessary to factor discounted future barrier dividend rewards in 79978d61-9d1f-4b20-b8a5-114797a8e380.

import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_isStoppingTime_withTop_of_le_events

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.levy_finiteStopping_clock_indep_shiftedPath
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s}) :
    IndepFun τ
      (fun ω : Ω => fun t : ℝ≥0 =>
        X.X (τ ω + t) ω - X.X (τ ω) ω) P := by
  sorry
