-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_simultaneous_good_event_lower
-- name    : AvramDividend.Classical.avram_a19_simultaneous_good_event_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:37:36.322889+00:00
-- url     : https://prove2.me/theorems/ca72093b-d996-4a05-90b1-e2c33f8056a8
-- title:
--   The common good event has probability at least five eighths
-- statement:
--   The complement of the union of an initial bad event and countably many bad increment events has probability at least five eighths when their probabilities are bounded as stated.
-- source:
--   A19 fixed-event geometric countermodel, countable complement measure.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_a19_simultaneous_bad_union_bound
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_a19_simultaneous_good_event_lower
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Set Ω) (E : Nat → Set Ω)
    (hBs : MeasurableSet B) (hEs : ∀ k, MeasurableSet (E k))
    (hB : P B ≤ (1 / 4 : ENNReal))
    (hE : tsum (fun k : Nat => P (E k)) ≤ (1 / 8 : ENNReal)) :
    (5 / 8 : ENNReal) ≤ P ((B ∪ Set.iUnion E)ᶜ) := by sorry
