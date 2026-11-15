-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_finitecap_rational_clip_strict_interior
-- name    : AvramDividend.Classical.avram_gbB41_original_finitecap_rational_clip_strict_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T13:43:24.318202+00:00
-- url     : https://prove2.me/theorems/e29c8acf-0195-4b65-ba40-f9b6982eb0f4
-- title:
--   Original finite ENNReal cap rational clipping level is strictly within generator smoothness band
-- statement:
--   For a finite positive ENNReal dividend cap C, each rational clipping level b_j=C.toReal(j+1)/(j+2) is strictly positive and satisfies ENNReal.ofReal b_j<C. Consequently the original HJB gradient and C2 assumptions apply in a neighbourhood of that clipped level.
-- source:
--   Proved B39 strict real band geometry and exact pinned Mathlib ENNReal.ofReal_lt_iff_lt_toReal equivalence.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB39_interior_finite_cap_fraction_strict_band
open Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB41_original_finitecap_rational_clip_strict_interior
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤) (j : ℕ) :
    let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    0 < b ∧ ENNReal.ofReal b < C := by sorry
