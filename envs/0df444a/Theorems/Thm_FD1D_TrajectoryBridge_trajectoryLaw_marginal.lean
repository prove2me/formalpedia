-- Prove2me | Theorems.Thm_FD1D_TrajectoryBridge_trajectoryLaw_marginal
-- name    : FD1D.TrajectoryBridge.trajectoryLaw_marginal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:45:40.353118+00:00
-- url     : https://prove2.me/theorems/d2c99ade-2122-5b75-8bb3-858bb41b3c5f
-- title:
--   Trajectory Bridge: trajectory Law marginal
-- statement:
--   The Trajectory Bridge construction uses the trajectory Law marginal property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/TrajectoryBridge.lean#L127-L137
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/TrajectoryBridge.lean#L127-L137

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Definitions.Def_FD1D_TrajectoryBridge
set_option autoImplicit true
open FD1D FD1D.TrajectoryBridge
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

theorem FD1D.TrajectoryBridge.trajectoryLaw_marginal
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) :
    Measure.map (fun path : ℕ → α => path n) (trajectoryLaw μ₀ κ) =
      iterateLaw κ μ₀ n := by sorry
