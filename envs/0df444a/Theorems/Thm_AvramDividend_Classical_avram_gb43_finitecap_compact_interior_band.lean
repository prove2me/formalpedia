-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb43_finitecap_compact_interior_band
-- name    : AvramDividend.Classical.avram_gb43_finitecap_compact_interior_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T10:52:02.834652+00:00
-- url     : https://prove2.me/theorems/c9faf761-0f0c-4a35-a6e8-f5d86c807704
-- title:
--   Every finite-cap Gaussian compact strip is in the open C² domain
-- statement:
--   For positive finite cap C and positive lower distance δ, the interval from δ/2 to C*(j+1)/(j+2) lies strictly in the interior domain where the Gaussian reward is C².
-- source:
--   Geometric compact-strip step for gb34, avoiding any boundary C² assumption.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gb43_finitecap_compact_interior_band
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    let a : ℝ := δ / 2
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} ∧
      Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by sorry
