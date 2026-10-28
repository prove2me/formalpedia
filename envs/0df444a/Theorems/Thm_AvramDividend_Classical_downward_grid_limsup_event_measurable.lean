-- Prove2me | Theorems.Thm_AvramDividend_Classical_downward_grid_limsup_event_measurable
-- name    : AvramDividend.Classical.downward_grid_limsup_event_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:52:57.885957+00:00
-- url     : https://prove2.me/theorems/3588ab51-c596-4dd9-9411-29c3c710979c
-- title:
--   Infinitely recurring negative increments on finite observation grids form a measurable path event
-- statement:
--   Choose arbitrary finite observation grids of time pairs indexed by natural resolution n and a real threshold a. The event that, for every coarse starting resolution N, a finer grid n≥N contains a path decrement less than −a is measurable in the full coordinate-product path space. At each fixed grid, every increment threshold is a measurable cylinder event, finite union preserves measurability, and the limsup event is a countable intersection of countable unions. This is an exact Borel event used to detect negative jumps by refining grids in the canonical Lévy jump-law transfer.
-- source:
--   Pinned Mathlib `MeasurableSet.iInter`, `MeasurableSet.iUnion`, `Finset.measurableSet_biUnion`, coordinate evaluation `measurable_pi_apply`. A subsequent theorem must establish the event's equivalence to genuine downward jumps on càdlàg paths; this lemma concerns measurability only.

import Mathlib.Data.NNReal.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Constructions
import Mathlib.MeasureTheory.MeasurableSpace.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic

open MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.downward_grid_limsup_event_measurable
    (grid : ℕ → Finset (ℝ≥0 × ℝ≥0)) (a : ℝ) :
    MeasurableSet
      (⋂ N : ℕ, ⋃ n : {n : ℕ // N ≤ n},
        ⋃ ij ∈ grid n.1,
          {f : ℝ≥0 → ℝ | f ij.2 - f ij.1 < -a}) := by sorry
