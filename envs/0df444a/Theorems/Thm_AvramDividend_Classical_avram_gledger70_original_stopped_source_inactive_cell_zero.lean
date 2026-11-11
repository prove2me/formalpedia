-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger70_original_stopped_source_inactive_cell_zero
-- name    : AvramDividend.Classical.avram_gledger70_original_stopped_source_inactive_cell_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T01:21:41.986775+00:00
-- url     : https://prove2.me/theorems/7b9e9a1d-61f4-41ec-8811-fc10a7936136
-- title:
--   Original clipped Gaussian physical mesh source is exactly zero after the stopping clock
-- statement:
--   Once the left endpoint of a deterministic physical source mesh cell lies after the original stopped clock, both clipped endpoints equal that clock, and the source discount and frozen-rightpayment reserve terminal terms coincide. This eliminates inactive cells exactly without integrability assumptions.
-- source:
--   Necessary inactive-cell branch of the gledger68 original physical-source observable-envelope package for gledger53. Source-exact clipping, no auxiliary process or limiting assumption.

import Mathlib
open MeasureTheory
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger70_original_stopped_source_inactive_cell_zero
    (Δ : ℝ≥0) (i : ℕ) (ρ : ℝ≥0)
    (q x : ℝ) (X D : ℝ≥0 → ℝ)
    (hinactive : ρ ≤ (i : ℝ≥0) * Δ) :
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    Real.exp (-(q * (v (i + 1) : ℝ))) =
        Real.exp (-(q * (v i : ℝ))) ∧
      x + X (v (i + 1)) - D (v i) =
        x + X (v i) - D (v i) := by sorry
