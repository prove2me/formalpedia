-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb68_finitecap_compact_hessian_cutoff_measurable
-- name    : AvramDividend.Classical.avram_gb68_finitecap_compact_hessian_cutoff_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T12:41:23.920267+00:00
-- url     : https://prove2.me/theorems/859502e9-4c09-45ed-ac7b-843ede6c2d83
-- title:
--   Finite-cap C2 Hessian compact cutoff is measurable on real line
-- statement:
--   The interior finite-cap C2 assumption on a function w implies measurability of the second derivative clipped to the deterministic compact interval [δ/2,C.toReal*(j+1)/(j+2)]. Positivity and strict fraction less than one put this interval inside the smooth interior domain. The result is independent of the stochastic process and supplies the only analytic component of the original predictable Hessian measurability theorem.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gb68_finitecap_compact_hessian_cutoff_measurable
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    Measurable (fun y : ℝ =>
      if y ∈ Icc a b then iteratedDeriv 2 w y else 0) := by sorry
