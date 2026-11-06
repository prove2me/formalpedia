-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid3_original_interior_point_explicit_compact_band
-- name    : AvramDividend.Classical.avram_p3_grid3_original_interior_point_explicit_compact_band
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:09:57.402778+00:00
-- url     : https://prove2.me/theorems/705128ce-f76b-4303-b746-496945e97f9c
-- title:
--   Explicit strict cap-interior compact band surrounding any positive original BV reserve
-- statement:
--   Any actual strictly positive reserve y below the original cap C admits a concrete compact band a=min(1,y), b=y, with 0<a≤2 and the wider [a/2,b] remaining strictly positive and below C. This discharges the geometric compact-band assumptions needed by the Proved original X.ν martingale/HJB signed source budget without assuming finite C or a global reserve margin.

import Mathlib.Data.ENNReal.Basic
open Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid3_original_interior_point_explicit_compact_band
    (C : ℝ≥0∞) (y : ℝ) (hy : 0 < y)
    (hyC : ENNReal.ofReal y < C) :
    let a : ℝ := min 1 y
    let b : ℝ := y
    0 < a ∧ a ≤ 2 ∧ a ≤ b ∧ y ∈ Set.Icc a b ∧
      Set.Icc (a / 2) b ⊆
        {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C} := by sorry
