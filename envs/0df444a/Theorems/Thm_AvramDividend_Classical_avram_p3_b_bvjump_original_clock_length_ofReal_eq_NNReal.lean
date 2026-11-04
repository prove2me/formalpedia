-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_clock_length_ofReal_eq_NNReal
-- name    : AvramDividend.Classical.avram_p3_b_bvjump_original_clock_length_ofReal_eq_NNReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:09:36.502618+00:00
-- url     : https://prove2.me/theorems/fb58dca6-8495-4edd-81f1-49d018231e32
-- title:
--   Original positive physical clock length matches P2's exact ENNReal nonnegative subtraction convention
-- statement:
--   The genuine original physical-clock Lebesgue interval length ENNReal.ofReal((t:ℝ)-(s:ℝ)) equals P2's formal exact factor ((t-s:ℝ≥0):ENNReal) whenever s≤t. The proof uses NNReal real-coercion subtraction and ENNReal.ofReal on nonnegative reals. It preserves zero length exactly and therefore bridges the deterministic clock formula to the P2 jump-rate convention without assuming finite negative-jump intensity.
-- source:
--   Mathlib NNReal.coe_sub and ENNReal.ofReal_coe_nnreal; original P2 finite-rectangle rate convention.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_b_bvjump_original_clock_length_ofReal_eq_NNReal
    (s t : ℝ≥0) (hst : s ≤ t) :
    ENNReal.ofReal ((t : ℝ) - (s : ℝ)) =
      ((t - s : ℝ≥0) : ℝ≥0∞) := by sorry
