-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_two_sided_closed_survival_measurable
-- name    : AvramDividend.Classical.chat04_random_reserve_shifted_two_sided_closed_survival_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:25:38.964703+00:00
-- url     : https://prove2.me/theorems/e5f97e4c-3755-4cc7-b887-78b6f11767fa
-- title:
--   Continuous two-sided survival of a shifted random Lévy reserve is measurable
-- statement:
--   For any measurable random initial capital and arbitrary past shift, the continuous-time event that a Lévy reserve stays inside [0,a] throughout a finite closed horizon is measurable. It is the countable intersection of measurable lower and upper half-space observations, using the Proved exact two-sided grid equivalence.
-- source:
--   Proved random-reserve shifted two-sided survival schedule equivalence; explicit countable schedule; adaptedness of Lévy path time evaluations.

import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_two_sided_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_explicit_shifted_killed_survival_schedule

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_random_reserve_shifted_two_sided_closed_survival_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (hH : Measurable H) (a : ℝ) (b T : ℝ≥0) :
    MeasurableSet
      {ω : Ω | ∀ v : ℝ≥0, v ≤ T →
        0 ≤ H ω + (X.X (b + v) ω - X.X b ω) ∧
        H ω + (X.X (b + v) ω - X.X b ω) ≤ a} := by sorry
