-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_locmoll_cap_extension
-- name    : AvramDividend.Classical.avram_locmoll_cap_extension
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-26T19:58:50.195479+00:00
-- url     : https://prove2.me/theorems/91e2f267-e335-4c51-88a8-93427319b32f
-- title:
--   Nonnegative monotone cap-linear extension for one-sided smoothing
-- statement:
--   Extend by unit slope above a finite cap and retain zero below zero. Reuses the proved cap-extension and zero-extension secant lemmas.
-- source:
--   Avram–Palmowski–Pistorius (2007), Proposition 4(i), child of 2e269e44-0ec4-4d09-bac9-26533bf1d8ab

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_locmoll_cap_extension
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    ∃ V : ℝ → ℝ,
      (∀ y : ℝ, ENNReal.ofReal y ≤ C → V y = w y) ∧
      (∀ y < 0, V y = 0) ∧ (∀ y, 0 ≤ V y) ∧ Monotone V ∧
      (∀ u v : ℝ, 0 ≤ u → u ≤ v → v - u ≤ V v - V u) := by sorry
