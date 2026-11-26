-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_shellTargetHeightFailure_subset_shellVariableTargetHeightFailure
-- name    : FirstPassageLinearTransport.shellTargetHeightFailure_subset_shellVariableTargetHeightFailure
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:55:02.137726+00:00
-- url     : https://prove2.me/theorems/224afb22-fb2a-485a-bc4d-3a9c085a1e02
-- title:
--   First Passage Linear Transport: shell Target Height Failure subset shell Variable Target Height Failure
-- statement:
--   The First Passage Linear Transport construction uses the shell Target Height Failure subset shell Variable Target Height Failure property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpJointExceptionalOrders.lean#L39-L55
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpJointExceptionalOrders.lean#L39-L55

import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.shellTargetHeightFailure_subset_shellVariableTargetHeightFailure
    {M : ℕ} {f u : ℕ → ℝ} {U : ℝ}
    (hu : ∀ n : ℕ, n ∈ dyadicShell M → u n ≤ U) :
    shellTargetHeightFailure M f U ⊆
      shellVariableTargetHeightFailure M f u := by sorry
