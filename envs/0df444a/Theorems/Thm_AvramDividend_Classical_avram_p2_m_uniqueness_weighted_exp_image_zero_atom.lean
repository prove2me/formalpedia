-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_weighted_exp_image_zero_atom
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_weighted_exp_image_zero_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T09:16:50.356637+00:00
-- url     : https://prove2.me/theorems/2ba07009-6d51-423d-a22e-37184354cc78
-- title:
--   Weighted exponential image has no mass at inaccessible zero
-- statement:
--   For any real Borel source measure σ, even an infinite Lévy rate, and arbitrary nonnegative ENNReal weight w, the weighted exponential image assigns zero mass to the singleton {0}. The exponential map has no zero preimage, so the atom vanishes without assuming any count intensity or moment convergence.

import Mathlib
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_m_uniqueness_weighted_exp_image_zero_atom (σ : Measure ℝ) (w : ℝ → ℝ≥0∞) : ((σ.withDensity w).map Real.exp) ({0} : Set ℝ) = 0 := by sorry
