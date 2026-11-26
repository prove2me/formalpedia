-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_normalized_card_shellVariableTargetHeightFailure_ge_reciprocal
-- name    : FirstPassageLinearTransport.normalized_card_shellVariableTargetHeightFailure_ge_reciprocal
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:56:29.59139+00:00
-- url     : https://prove2.me/theorems/ebadce1c-a0f5-4350-8ff4-10fde8127c84
-- title:
--   First Passage Linear Transport: normalized card shell Variable Target Height Failure ge reciprocal
-- statement:
--   The exact reciprocal moving-shell obstruction with a variable displayed
--   ceiling, bounded above on the shell by `U`.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpJointExceptionalOrders.lean#L59-L82
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpJointExceptionalOrders.lean#L59-L82

import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.normalized_card_shellVariableTargetHeightFailure_ge_reciprocal
    {M h : ℕ} (hhM : h ≤ M) (hh : 0 < h)
    {U : ℝ} (hU : 1 ≤ U)
    (hlog : Real.log U ≤
      reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3)
    {f u : ℕ → ℝ}
    (htarget : ∀ n : ℕ, n ∈ dyadicShell M →
      f n < (n : ℝ) / (2 : ℝ) ^ h)
    (hu : ∀ n : ℕ, n ∈ dyadicShell M → u n ≤ U) :
    (2 / (3 * U)) *
        (1 - reciprocalMaximumConstant / (h : ℝ)) ≤
      ((shellVariableTargetHeightFailure M f u).card : ℝ) /
        (2 : ℝ) ^ M := by sorry
