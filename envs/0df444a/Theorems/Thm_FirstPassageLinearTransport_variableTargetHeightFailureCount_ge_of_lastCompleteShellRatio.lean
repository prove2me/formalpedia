-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_variableTargetHeightFailureCount_ge_of_lastCompleteShellRatio
-- name    : FirstPassageLinearTransport.variableTargetHeightFailureCount_ge_of_lastCompleteShellRatio
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:55:42.490034+00:00
-- url     : https://prove2.me/theorems/93d0569c-d638-4b1d-a217-ddebbf017046
-- title:
--   First Passage Linear Transport: variable Target Height Failure Count ge of last Complete Shell Ratio
-- statement:
--   A normalized lower bound on the last complete shell loses at most the
--   fixed factor four when converted to the whole prefix.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpJointExceptionalOrders.lean#L166-L194
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpJointExceptionalOrders.lean#L166-L194

import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.variableTargetHeightFailureCount_ge_of_lastCompleteShellRatio
    {X : ℕ} (hX : 4 ≤ X) {f u : ℕ → ℝ} {b : ℝ} (hb : 0 ≤ b)
    (hShell : b ≤
      ((shellVariableTargetHeightFailure
        (lastCompleteDyadicShell X) f u).card : ℝ) /
          (2 : ℝ) ^ lastCompleteDyadicShell X) :
    (b / 4) * (X : ℝ) ≤ variableTargetHeightFailureCount f u X := by sorry
