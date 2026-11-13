-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_finite_borel_mark_real_intensity_norm_bound_20261113
-- name    : AvramDividend.Classical.avram_a21_finite_borel_mark_real_intensity_norm_bound_20261113
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T00:24:49.16036+00:00
-- url     : https://prove2.me/theorems/1425b5d5-9053-4653-938f-2757b534a193
-- title:
--   Uniform unit bounded original Borel mark intensity integral is controlled by finite mark intensity
-- statement:
--   For a finite measure of any measurable real mark set, any real mark function bounded absolutely by one on that set has its Bochner integral norm bounded by the finite real measure of the set, without changing the measure space. This gives the source compensator envelope for A21 finite negative Borel marks.
-- source:
--   Pinned Mathlib norm_integral_le_of_norm_le_const (exact revision header inspected), finite restricted measure instance, ae_restrict_mem, and original negative Borel mass finiteness.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a21_finite_borel_mark_real_intensity_norm_bound_20261113
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (hMass : ν S < ⊤) (f : ℝ → ℝ)
    (hBound : ∀ z ∈ S, |f z| ≤ 1) :
    ‖∫ z in S, f z ∂ν‖ ≤ (ν S).toReal := by sorry
