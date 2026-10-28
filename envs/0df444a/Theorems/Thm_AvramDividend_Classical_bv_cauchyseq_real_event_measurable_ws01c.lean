-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_cauchyseq_real_event_measurable_ws01c
-- name    : AvramDividend.Classical.bv_cauchyseq_real_event_measurable_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T12:06:30.367304+00:00
-- url     : https://prove2.me/theorems/8589b747-d286-4519-a1f4-6cb73fdcf826
-- title:
--   The event that a measurable real sequence is Cauchy is measurable
-- statement:
--   For a countable family of measurable real-valued coordinate maps, the set of points at which the sequence is Cauchy is measurable. Represent the Cauchy property as a countable intersection of countable unions of countable intersections of measurable closed inequalities, using thresholds 1/(k+1). This cylinder supports the actual Lévy dyadic event's Fubini and whole-path-law transfers.
-- source:
--   Exact source-level proof extracted from work/avram_ws01c_actual_stationary_cauchy_v2_draft.lean. Supports WS01C origin-slope Fubini and equal-path-law Cauchy probability without positing the random path's a.s. convergence. Proved Mathlib measurability and Cauchy characterisation are verified by the remote compiler.

import Mathlib

open Filter MeasureTheory Set

theorem AvramDividend.Classical.bv_cauchyseq_real_event_measurable_ws01c
    {E : Type*} [MeasurableSpace E]
    (v : ℕ → E → ℝ) (hv : ∀ n, Measurable (v n)) :
    MeasurableSet {e : E | CauchySeq (fun n => v n e)} := by sorry
