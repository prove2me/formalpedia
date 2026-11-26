-- Prove2me | Theorems.Thm_FD1D_TrajectoryBridge_trajectoryLaw_marginal_succ
-- name    : FD1D.TrajectoryBridge.trajectoryLaw_marginal_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:11:34.634617+00:00
-- url     : https://prove2.me/theorems/cb076d90-326c-582d-97a1-65f13ece7e03
-- title:
--   Trajectory Bridge: trajectory Law marginal succ
-- statement:
--   The Trajectory Bridge construction uses the trajectory Law marginal succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/TrajectoryBridge.lean#L85-L125
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/TrajectoryBridge.lean#L85-L125

import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Definitions.Def_FD1D_TrajectoryBridge
set_option autoImplicit true
open FD1D FD1D.TrajectoryBridge
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ENNReal
variable {α : Type*} [MeasurableSpace α]

theorem FD1D.TrajectoryBridge.trajectoryLaw_marginal_succ
    (μ₀ : Measure α) [IsProbabilityMeasure μ₀]
    (κ : Kernel α α) [IsMarkovKernel κ] (n : ℕ) :
    Measure.map (fun path : ℕ → α => path (n + 1)) (trajectoryLaw μ₀ κ) =
      κ ∘ₘ Measure.map (fun path : ℕ → α => path n) (trajectoryLaw μ₀ κ) := by sorry
