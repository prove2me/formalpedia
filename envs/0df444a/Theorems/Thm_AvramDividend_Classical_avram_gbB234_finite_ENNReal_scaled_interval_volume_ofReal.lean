-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB234_finite_ENNReal_scaled_interval_volume_ofReal
-- name    : AvramDividend.Classical.avram_gbB234_finite_ENNReal_scaled_interval_volume_ofReal
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:27:13.27998+00:00
-- url     : https://prove2.me/theorems/d6bed311-b48a-4753-aacf-245aace515d2
-- title:
--   Finite ENNReal bound times real open interval volume equals the ofReal-scaled interval length
-- statement:
--   For any finite nonnegative extended-real bound B, the product of B and Lebesgue volume on the real open interval (a,b) equals ofReal of the real product of B.toReal and b-a; valid even when the interval is empty. This exact deterministic normalisation converts occupation densities to the GB227 bound.
-- source:
--   Mathlib Real.volume_Ioo, ENNReal.ofReal_toReal and ENNReal.ofReal_mul.

import Mathlib
open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB234_finite_ENNReal_scaled_interval_volume_ofReal
    (B : ℝ≥0∞) (hB : B ≠ ⊤) (a b : ℝ) :
    B * volume (Set.Ioo a b) =
      ENNReal.ofReal (B.toReal * (b - a)) := by sorry
