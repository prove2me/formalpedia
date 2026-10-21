-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_upper_before_horizon_measurable
-- name    : AvramDividend.Classical.chat03_upper_before_horizon_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:20:24.353083+00:00
-- url     : https://prove2.me/theorems/d3c94455-e986-4690-a6a0-a03e0da6794d
-- title:
--   Strict upward crossing before a deterministic finite horizon is a measurable event
-- statement:
--   For each real upper crossing threshold and finite NNReal horizon T, the event that an official adapted spectrally negative Lévy process exceeds the threshold strictly at some time s<T is measurable in the ambient sigma algebra. The already Proved horizon-preserving countable inverse-natural grid detection theorem reduces this continuous-time event to a countable union of measurable deterministic-time upper-exit events with constant grid-time condition k/n<T. This is the required finite-horizon event bridge for strict first-passage clock measurability.
-- source:
--   Proved chat03_upper_before_horizon_countable_grid_iff, official X.adapted and pinned Mathlib measurableSet_lt and MeasurableSet.iUnion.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_horizon_countable_grid_iff
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_upper_before_horizon_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (upper : ℝ) (T : ℝ≥0) :
    MeasurableSet {ω : Ω | ∃ s : ℝ≥0,
      s < T ∧ upper < X.X s ω} := by sorry
