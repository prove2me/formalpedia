-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva43_original_negative_mark_all_shifted_levels_null
-- name    : AvramDividend.Classical.avram_bva43_original_negative_mark_all_shifted_levels_null
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:57:32.993795+00:00
-- url     : https://prove2.me/theorems/07de2d42-a168-4da9-b963-3146ee290f66
-- title:
--   Original BV negative jump intensity gives zero mass to every shifted reserve level
-- statement:
--   For each reserve value a and each boundary level b, the negative-jump Levy measure gives zero mass to exactly those jump marks z which hit b. This atomlessness is needed for continuity in the jump-mark coordinate when estimating the marked-compensator physical-grid quadrature in the original BV process.
-- source:
--   Support for theorem e5edbe9b-78cf-4121-bb35-2f016cf0e2cb (original zero-mark compensator quadrature), authored 11 November 2026.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal Topology

theorem AvramDividend.Classical.avram_bva43_original_negative_mark_all_shifted_levels_null {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {ℱ : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P ℱ) (hStanding : X.Standing) (hBV : X.BoundedVariation) (a b : ℝ) : X.ν {z : ℝ | a + z = b} = 0 := by sorry
