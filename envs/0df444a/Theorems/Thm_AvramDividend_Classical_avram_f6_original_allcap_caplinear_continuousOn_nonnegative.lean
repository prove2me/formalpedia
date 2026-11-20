-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_allcap_caplinear_continuousOn_nonnegative
-- name    : AvramDividend.Classical.avram_f6_original_allcap_caplinear_continuousOn_nonnegative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T17:23:47.881186+00:00
-- url     : https://prove2.me/theorems/11ee3303-0213-43be-b49d-beb25251c487
-- title:
--   Original caplinear all-cap HJB w continuation continuous on nonnegative reserves
-- statement:
--   For w continuous on nonnegative reserves, its exact original HJB capped linear continuation z↦ if ENNReal.ofReal z ≤ C then w z else w C.toReal+(z-C.toReal) is continuous on nonnegative reserves for finite or infinite cap. Both branches agree at the finite cap contact, preserving the exact original reserve convention.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_allcap_caplinear_continuousOn_nonnegative
    (w : ℝ → ℝ) (hw : ContinuousOn w (Ici 0))
    (C : ℝ≥0∞) :
    ContinuousOn
      (fun z : ℝ => if ENNReal.ofReal z ≤ C then w z
         else w C.toReal + (z - C.toReal)) (Ici 0) := by sorry
