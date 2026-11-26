-- Prove2me | Theorems.Thm_FD1D_TrajectoryBridge_trajectoryLaw_marginal_zero
-- name    : FD1D.TrajectoryBridge.trajectoryLaw_marginal_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:07:34.949908+00:00
-- url     : https://prove2.me/theorems/8329d3b0-3b2b-4654-b5b4-c72f6d22cf91
-- title:
--   Trajectory Bridge: trajectory Law marginal zero
-- statement:
--   The Trajectory Bridge construction uses the trajectory Law marginal zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/TrajectoryBridge.lean#L51-L83
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/TrajectoryBridge.lean#L51-L83

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Definitions.Def_FD1D_TrajectoryBridge
set_option autoImplicit true
open FD1D FD1D.TrajectoryBridge
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

theorem FD1D.TrajectoryBridge.trajectoryLaw_marginal_zero
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (κ : Kernel α α) [IsMarkovKernel κ] :
    Measure.map (fun path : ℕ → α => path 0) (trajectoryLaw μ₀ κ) = μ₀ := by sorry
