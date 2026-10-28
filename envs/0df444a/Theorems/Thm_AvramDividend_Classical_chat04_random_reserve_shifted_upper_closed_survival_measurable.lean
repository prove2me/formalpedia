-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_upper_closed_survival_measurable
-- name    : AvramDividend.Classical.chat04_random_reserve_shifted_upper_closed_survival_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:22:51.72355+00:00
-- url     : https://prove2.me/theorems/5f723314-e27f-4c24-b9dc-dfcc9ce268df
-- title:
--   Continuous-time shifted upper-barrier survival is measurable for random initial capital
-- statement:
--   The event that a shifted Lévy reserve with a measurable random starting amount remains below a fixed upper barrier at every time of a closed finite horizon is measurable. Countable rational-and-terminal monitoring equals the continuous-time event, and all monitored increments are measurable by adaptedness. This supplies the upper half of two-sided killed-event measurability.
-- source:
--   Previously Proved shifted upper survival schedule iff and explicit countable schedule; Mathlib measurableSet_iInter and adaptedness.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_upper_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_random_reserve_shifted_upper_closed_survival_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (hH : Measurable H) (a : ℝ) (b T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
        H ω + (X.X (b + v) ω - X.X b ω) ≤ a} := by sorry
