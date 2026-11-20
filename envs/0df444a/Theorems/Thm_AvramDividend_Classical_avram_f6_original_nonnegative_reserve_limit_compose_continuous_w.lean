-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_nonnegative_reserve_limit_compose_continuous_w
-- name    : AvramDividend.Classical.avram_f6_original_nonnegative_reserve_limit_compose_continuous_w
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T16:10:35.030964+00:00
-- url     : https://prove2.me/theorems/6e30c0e4-3794-4d4a-ad44-99537df70abe
-- title:
--   Continuous HJB w transfers eventually nonnegative rightmesh reserve convergence
-- statement:
--   For the original HJB test function continuous on nonnegative reserves, an eventually nonnegative real reserve sequence converging to a nonnegative physical postpayment reserve has convergent w-values. This exactly captures the 0-boundary/topology issue in original pre-ruin terminal rightmesh contact, without assuming continuity from negative reserve.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_nonnegative_reserve_limit_compose_continuous_w
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (f : ℕ → ℝ) (y : ℝ)
    (hy : 0 ≤ y)
    (hf : Tendsto f atTop (𝓝 y))
    (hpos : ∀ᶠ m : ℕ in atTop, 0 ≤ f m) :
    Tendsto (fun m => w (f m)) atTop (𝓝 (w y)) := by sorry
