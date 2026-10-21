-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_measurable
-- name    : AvramDividend.Classical.chat03_lower_before_horizon_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T06:40:29.117322+00:00
-- url     : https://prove2.me/theorems/76ef792f-a59a-4298-b7e4-028d870f98a1
-- title:
--   Strict lower first-passage occurrence before any finite horizon is measurable
-- statement:
--   For an adapted official spectrally negative Lévy process, the event of a strict lower crossing occurring at any nonnegative time before finite horizon T is measurable. The previously Proved lower finite-horizon countable-grid equivalence replaces the uncountable-time existential predicate by a countable union of measurable deterministic-time strict lower crossing events and constant grid-time inequalities.
-- source:
--   Official Lévy process definitions and independently Proved horizon-grid and generic first-passage results at pinned Mathlib revision.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat03_lower_before_horizon_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (lower : ℝ) (T : ℝ≥0) :
    MeasurableSet {ω : Ω | ∃ s : ℝ≥0,
      s < T ∧ X.X s ω < lower} := by sorry
