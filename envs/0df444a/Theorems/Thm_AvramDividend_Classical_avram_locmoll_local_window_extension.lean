-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_local_window_extension
-- name    : AvramDividend.Classical.avram_locmoll_local_window_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T21:41:47.251079+00:00
-- url     : https://prove2.me/theorems/d7c98a61-091b-52dc-baa6-3e3e0e56b9ea
-- title:
--   Compact C2 replacement on all translates near a fixed interior evaluation point
-- statement:
--   Compact C2 replacement on all translates near a fixed interior evaluation point
-- source:
--   Avram Proposition 4(i), child of 06cb2549-7f74-48bc-a6ba-0890037b26d6

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology Convolution
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_local_window_extension
    (w V : ℝ → ℝ) (C : ℝ≥0∞) (δ y : ℝ)
    (hδ : 0 < δ) (hy : δ ≤ y) (hyC : ENNReal.ofReal y ≤ C)
    (hw : ContDiffOn ℝ 2 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hV : ∀ z : ℝ, ENNReal.ofReal z ≤ C → V z = w z) :
    ∃ F : ℝ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport F ∧
      (∀ z ∈ Ioo (y - 5 * δ / 6) (y - δ / 6), F z = w z ∧ V z = w z) := by sorry
