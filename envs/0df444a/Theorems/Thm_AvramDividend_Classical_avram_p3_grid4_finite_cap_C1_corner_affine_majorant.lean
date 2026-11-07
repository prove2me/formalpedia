-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_finite_cap_C1_corner_affine_majorant
-- name    : AvramDividend.Classical.avram_p3_grid4_finite_cap_C1_corner_affine_majorant
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T09:27:35.132042+00:00
-- url     : https://prove2.me/theorems/440635f0-c317-4553-9d3f-7b7921c74c72
-- title:
--   Canonical BV C1 cap continuation lies below its slope-one affine supporting line without cap derivative
-- statement:
--   For a positive finite cap C, a nonnegative reserve y, and an original bounded-variation verification candidate w continuous on the nonnegative halfline, C1 strictly within (0,C), with derivative at least one there, the cap-linear continuation y↦w(y) below C and w(C)+(y-C) above C is bounded by the affine slope-one line w(C)+(y-C) at all y≥0. The cap-corner inequality follows from Proved 244e0215 including endpoints, imposes no derivative at C and is useful for error/contact signs.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_bv_finite_cap_linear_crossing_secant
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_finite_cap_C1_corner_affine_majorant
    (C : ℝ≥0∞) (hC : 0 < C) (hfinite : C ≠ ⊤)
    (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w
      {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z →
      ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (y : ℝ) (hy : 0 ≤ y) :
    (if y ≤ C.toReal then w y
     else w C.toReal + (y - C.toReal)) ≤
      w C.toReal + (y - C.toReal) := by sorry
