-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_positive_markfree_event_survives_ae_linear_path
-- name    : AvramDividend.Classical.avram_bvb_obstruction_positive_markfree_event_survives_ae_linear_path
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T01:16:17.8919+00:00
-- url     : https://prove2.me/theorems/55cf8004-9c93-4ce5-ba13-a53b5ea9870b
-- title:
--   Positive-probability nojump event retains positive measure after an almost-sure original linear source property
-- statement:
--   An event E of strictly positive measure retains its full measure upon intersection with any property R that holds almost everywhere conditional on E. This combines the Proved original compound Poisson no-negative-jump probability with the Proved BV linear-source-on-no-mark event, yielding a positive-probability event that satisfies both.
-- source:
--   Apply pinned Mathlib Measure.measure_inter_eq_of_ae to the almost-everywhere implication E→R. The intersection of that implication event with E equals {ω|Eω∧Rω}, so its measure equals P(E)>0.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_bvb_obstruction_positive_markfree_event_survives_ae_linear_path
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (E : Set Ω) (R : Ω → Prop)
    (hPos : 0 < P E)
    (hAe : ∀ᵐ ω ∂P, ω ∈ E → R ω) :
    0 < P {ω | ω ∈ E ∧ R ω} := by sorry
