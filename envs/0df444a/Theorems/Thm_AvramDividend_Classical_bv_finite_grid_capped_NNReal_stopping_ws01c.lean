-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_grid_capped_NNReal_stopping_ws01c
-- name    : AvramDividend.Classical.bv_finite_grid_capped_NNReal_stopping_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:44:25.884237+00:00
-- url     : https://prove2.me/theorems/377a241b-e6e4-4c2f-b968-3f914d9839f9
-- title:
--   Finite-list capped lower-observation clock is a stopping time in the original filtration
-- statement:
--   The finite NNReal first-lower-crossing observation clock, whose list times stay within a deterministic fallback H, remains a stopping time in the actual original filtration after capping at finite T. The proof inducts over observation minima and the published adapted two-valued observation clock, without assuming the raw lower exit clock itself is an original-filtration stopping time.
-- source:
--   Existing mathematically necessary named theorem from work/avram_ws01c_finite_clock_nnreal_adapter_draft.lean. Uses confirmed public definition bundle 2d81875c-9b5a-4bad-903c-074da5c0eaa7 and canonically Proved bv_observation_or_horizon_stopping_ws01c UUID 30032f11-a174-4e96-a28d-121bce9cdbdd. Complete adapted-list inductive proof work/avram_ws01c_finite_grid_capped_stop_solution_20261028.lean.

import Mathlib
import Definitions.Def_AvramDividend_Classical_BvFiniteGridClocks_ws01c
import Theorems.Thm_AvramDividend_Classical_bv_observation_or_horizon_stopping_ws01c

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_grid_capped_NNReal_stopping_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (ℱ : Filtration ℝ≥0 mΩ)
    (Y : ℝ≥0 → Ω → ℝ) (b : ℝ) (H T : ℝ≥0)
    (L : List ℝ≥0)
    (hL : ∀ t ∈ L, t ≤ H)
    (hY : ∀ t, Measurable[ℱ t] (Y t)) :
    IsStoppingTime ℱ
      (fun ω => (((bv_finite_grid_below_NNReal_ws01c Y b H L ω) ⊓ T) :
        WithTop ℝ≥0)) := by sorry
