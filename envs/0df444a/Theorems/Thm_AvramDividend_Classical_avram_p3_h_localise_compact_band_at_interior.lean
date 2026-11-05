-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_h_localise_compact_band_at_interior
-- name    : AvramDividend.Classical.avram_p3_h_localise_compact_band_at_interior
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T12:57:54.559779+00:00
-- url     : https://prove2.me/theorems/5ae2944f-b0bf-4c1c-ba25-1ad2b4e425f2
-- title:
--   Every strict original positive reserve has a compact cap-interior stopped-compensator band
-- statement:
--   Each positive reserve point below an arbitrary finite or infinite cap belongs to a compact interval whose enlarged left strip remains in the exact strict positive-cap generator region, with a ≤ 2. Supplies the missing geometry for the original P3-G Lipschitz and P3-E stopped-compensator localisation interfaces.
-- source:
--   Elementary real interval geometry and monotonicity of ENNReal.ofReal; no probability assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_h_localise_compact_band_at_interior
    (C : ℝ≥0∞) (z : ℝ)
    (hz : 0 < z) (hzC : ENNReal.ofReal z < C) :
    ∃ a b : ℝ, 0 < a ∧ a ≤ 2 ∧ a ≤ b ∧ z ∈ Icc a b ∧
      Icc (a / 2) b ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by sorry
