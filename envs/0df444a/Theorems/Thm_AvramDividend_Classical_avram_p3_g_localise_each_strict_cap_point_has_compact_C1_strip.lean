-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_each_strict_cap_point_has_compact_C1_strip
-- name    : AvramDividend.Classical.avram_p3_g_localise_each_strict_cap_point_has_compact_C1_strip
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:27:02.39024+00:00
-- url     : https://prove2.me/theorems/325f33e2-a16b-4da8-b618-5dcbf2b982e8
-- title:
--   Every strictly positive original reserve below a finite or infinite cap lies in a derivative-safe compact interior strip
-- statement:
--   For any strictly positive reserve y with original cap condition ENNReal.ofReal y < C, construct explicit finite strip a ≤ y ≤ b with 0<a≤2 and the larger derivative band [a/2,b] wholly inside the original C1 domain. This works uniformly for finite and infinite caps and does not include zero or a finite-cap contact in a strict-interior strip.
-- source:
--   Elementary compact localisation of the exact physical C1 region of the classical dividend target; uses the pinned ENNReal.ofReal_le_ofReal theorem. No stochastic occupation assumption.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p3_g_localise_each_strict_cap_point_has_compact_C1_strip (C : ℝ≥0∞) (y : ℝ)
    (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧ y ∈ Icc a b ∧
      Icc (a / 2) b ⊆
        {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} := by sorry
