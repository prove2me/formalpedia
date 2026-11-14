-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb42_original_finite_negative_mark_times_terminal_margin
-- name    : AvramDividend.Classical.avram_bvb42_original_finite_negative_mark_times_terminal_margin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T12:26:16.25309+00:00
-- url     : https://prove2.me/theorems/18c235bc-9895-422c-9682-ff657d10f30c
-- title:
--   Finite original physical negative jump times have a terminal no-arrival strip when the fixed horizon carries no mark
-- statement:
--   For an actual finite-count negative-mark physical time set and a deterministic physical terminal time that is not itself an original mark, there exists a strictly positive real width such that every genuine mark at or before that horizon is at least this width before the horizon. This follows directly from previously Proved bva51 real Finset representation and bva41 finite separation applied with terminal time inserted. It supports finite negative-jump localisation and permits excluding terminal contact jumps without changing the original clock.
-- source:
--   The original physical negative jump-time count 84c8c695 and finite real mark enumerator a5fc8350, finite separation 539a67f9. Terminal fixed-time no-atom premise remains explicit.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_bva51_finite_count_mark_times_real_finset
import Theorems.Thm_AvramDividend_Classical_avram_bva41_finite_distinct_mark_times_positive_gap
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb42_original_finite_negative_mark_times_terminal_margin
    (S : Set ℝ≥0)
    (hCount : (Measure.count S) < ⊤)
    (T : ℝ) (hT : 0 ≤ T)
    (hNoTerminal : (⟨T,hT⟩ : ℝ≥0) ∉ S) :
    ∃ δ : ℝ, 0 < δ ∧
      ∀ t : ℝ≥0, t ∈ S → (t : ℝ) ≤ T → (t : ℝ) ≤ T - δ := by sorry
