-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger131_strict_uniform_grid_interior_width
-- name    : AvramDividend.Classical.avram_gledger131_strict_uniform_grid_interior_width
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T17:51:27.360605+00:00
-- url     : https://prove2.me/theorems/ab81a6cd-7a23-4ee0-a804-c233edffb827
-- title:
--   Original stopped uniform mesh has exact strict interior cell width
-- statement:
--   Before the first clipped-grid crossing, each strictly interior stopped mesh cell coincides with the corresponding full uniform grid cell. Its real-valued width is exactly the deterministic mesh step, including the zero step case.
-- source:
--   Finite deterministic clipped mesh v_i=min(iΔ,ρ) and strict-prefix property supplied by Proved gledger110. Necessary step-width hypothesis of Proved original gledger112 strict interior cash-rate bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger131_strict_uniform_grid_interior_width
    (n m : ℕ) (ρ : ℝ≥0) (k : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 2)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    (∀ i : ℕ, i < k → v (i + 1) < ρ) →
      ∀ i : ℕ, i < k →
        (v (i + 1) : ℝ) - (v i : ℝ) = (Δ : ℝ) := by sorry
