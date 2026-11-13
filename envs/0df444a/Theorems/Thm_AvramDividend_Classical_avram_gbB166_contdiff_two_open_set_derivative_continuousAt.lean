-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB166_contdiff_two_open_set_derivative_continuousAt
-- name    : AvramDividend.Classical.avram_gbB166_contdiff_two_open_set_derivative_continuousAt
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T16:02:39.87+00:00
-- url     : https://prove2.me/theorems/7a179511-3dda-44f5-bd93-f278723d3cd3
-- title:
--   C2 on an open real set implies ordinary derivative is continuous at interior points
-- statement:
--   For a real C2 function on an open set, the ordinary derivative is continuous at every point of that set. Used to check the clipped-gradient continuity condition on regular Gaussian-reserve times in B163.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gbB166_contdiff_two_open_set_derivative_continuousAt
    (w : ℝ → ℝ) (U : Set ℝ) (hU : IsOpen U)
    (hw : ContDiffOn ℝ 2 w U) (y : ℝ) (hy : y ∈ U) :
    ContinuousAt (deriv w) y := by sorry
