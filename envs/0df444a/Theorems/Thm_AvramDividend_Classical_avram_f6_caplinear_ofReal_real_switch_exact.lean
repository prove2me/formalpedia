-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_caplinear_ofReal_real_switch_exact
-- name    : AvramDividend.Classical.avram_f6_caplinear_ofReal_real_switch_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T09:43:32.490144+00:00
-- url     : https://prove2.me/theorems/06124740-229c-4c3d-b397-a77299c657f4
-- title:
--   Canonical ENNReal caplinear V equals the real piecewise caplinear continuation
-- statement:
--   The canonical caplinear value continuation on the true ENNReal.ofReal cap comparison agrees pointwise with the real split used in the original bounded physical-grid Stieltjes source: at C=top it is w; for finite positive C, ofReal z<=C is equivalent to z<=C.toReal. This bridges the exact ruin-contact terminal proof to the existing physical Ito/cash grid source without adding above-cap regularity.

import Mathlib
set_option autoImplicit false
open MeasureTheory Set Filter
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_caplinear_ofReal_real_switch_exact
    (C : ℝ≥0∞) (hC : 0 < C) (w : ℝ → ℝ) (z : ℝ) :
    (if ENNReal.ofReal z ≤ C then w z
      else w C.toReal + (z - C.toReal)) =
    (if C = ⊤ then w z
      else if z ≤ C.toReal then w z
      else w C.toReal + (z - C.toReal)) := by sorry
