-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_count_restrict_map_rectangle
-- name    : AvramDividend.Classical.avram_p2_c_borel_count_restrict_map_rectangle
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:30:50.306697+00:00
-- url     : https://prove2.me/theorems/d3c582e3-ef1b-43fb-a635-7e2e2436ea03
-- title:
--   Intrinsic mapped counting-measure rectangle equals count of restricted time-mark preimage
-- statement:
--   For an arbitrary measurable marked-time map, the literal count measure restricted to an intrinsic set of candidate jumps and mapped into time-mark space evaluates a Borel rectangle as the original counting measure of jump indices satisfying both the intrinsic restriction and rectangle tests. The identity is exact before expectation and needs neither a compensator nor any Levy source rate.
-- source:
--   P2-C direct elementary measure transport from pinned Measure.map_apply and Measure.restrict_apply; applies to the actual intrinsic jump-time selector after measurability is established, and is independent of the Open original Levy rate target 34dbea70.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_c_borel_count_restrict_map_rectangle
    {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ]
    (jump : α → β × γ) (hjump : Measurable jump)
    (J : Set α) (time : Set β) (marks : Set γ)
    (htime : MeasurableSet time) (hmarks : MeasurableSet marks) :
    ((Measure.count.restrict J).map jump) (time ×ˢ marks) =
      Measure.count {u : α | u ∈ J ∧ jump u ∈ time ×ˢ marks} := by sorry
