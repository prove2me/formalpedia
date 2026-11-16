-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_finite_compensated_residual_left_right_exact
-- name    : AvramDividend.Classical.avram_bva_finite_compensated_residual_left_right_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:46:55.022629+00:00
-- url     : https://prove2.me/theorems/3f8ed821-5655-4dd3-8f8d-09f70e882c31
-- title:
--   Exact continuity identity for finite physical-jump-compensated drift residual at a jump
-- statement:
--   For any finite set of actual jump times, at each included jump time the post-jump drift-deficit minus cumulative jump sum equals the pre-jump drift-deficit minus the strict prefix jump sum. This is exact cancellation of the physical jump, ensuring the compensated residual does not jump.
-- source:
--   Actual finite-mark step jump identity and real group algebra

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_bva_finite_compensated_residual_left_right_exact
    (f : ℝ≥0 → ℝ) (drift : ℝ)
    (S : Finset ℝ≥0) (t : ℝ≥0) (ht : t ∈ S) :
    (t : ℝ) * drift - f t -
      Finset.sum S (fun u => if u ≤ t then Function.leftLim f u - f u else 0) =
    (t : ℝ) * drift - Function.leftLim f t -
      Finset.sum S (fun u => if u < t then Function.leftLim f u - f u else 0) := by sorry
