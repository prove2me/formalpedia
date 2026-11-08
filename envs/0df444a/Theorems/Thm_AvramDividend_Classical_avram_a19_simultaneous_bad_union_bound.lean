-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a19_simultaneous_bad_union_bound
-- name    : AvramDividend.Classical.avram_a19_simultaneous_bad_union_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:11:50.154141+00:00
-- url     : https://prove2.me/theorems/a6669ed8-78e4-48df-aeb8-568b30d52e66
-- title:
--   Countable bad-increment events have one small union
-- statement:
--   One initial bad event of probability at most one quarter and countably many bad increment events with total probability at most one eighth together have probability at most three eighths.
-- source:
--   A19 fixed-event source countermodel, countable subadditivity.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_a19_simultaneous_bad_union_bound
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (B : Set Ω) (E : Nat → Set Ω)
    (hB : P B ≤ (1 / 4 : ENNReal))
    (hE : tsum (fun k : Nat => P (E k)) ≤ (1 / 8 : ENNReal)) :
    P (B ∪ Set.iUnion E) ≤ (3 / 8 : ENNReal) := by sorry
