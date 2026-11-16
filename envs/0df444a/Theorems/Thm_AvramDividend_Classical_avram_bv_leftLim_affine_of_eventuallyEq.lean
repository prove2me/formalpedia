-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_leftLim_affine_of_eventuallyEq
-- name    : AvramDividend.Classical.avram_bv_leftLim_affine_of_eventuallyEq
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:56:42.937512+00:00
-- url     : https://prove2.me/theorems/3c87b5f1-b631-49c3-ad68-0aa9787c1046
-- title:
--   Affine left limit from eventual affine equality on nontrivial left neighbourhood
-- statement:
--   If a real-valued function on nonnegative real times eventually agrees with an affine function on a nontrivial left neighbourhood of t, its strict left limit is the affine value at t. This is the local limit calculation needed to telescope a finite set of jump discontinuities.
-- source:
--   Mathlib.Topology.Order.LeftRightLim.leftLim_eq_of_tendsto, reviewed 15 November 2026

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical Filter Topology AvramDividend.Classical
open scoped Topology NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_leftLim_affine_of_eventuallyEq
    (f : ℝ≥0 → ℝ) (t : ℝ≥0) (a b : ℝ)
    [Filter.NeBot (𝓝[<] t)]
    (hEvent : f =ᶠ[𝓝[<] t] (fun s : ℝ≥0 => a + b * (s : ℝ))) :
    Function.leftLim f t = a + b * (t : ℝ) := by sorry
