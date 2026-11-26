-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_variableTargetHeightFailureCount_ge_reciprocal_lastCompleteShell
-- name    : FirstPassageLinearTransport.variableTargetHeightFailureCount_ge_reciprocal_lastCompleteShell
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T12:55:19.410144+00:00
-- url     : https://prove2.me/theorems/49152a31-fbaf-5239-bbb5-eee6d3d47a90
-- title:
--   First Passage Linear Transport: variable Target Height Failure Count ge reciprocal last Complete Shell
-- statement:
--   Quantitative global consumer of the exact reciprocal shell obstruction.
--   All profile-specific work is isolated in the four hypotheses imposed on the
--   last complete shell.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpJointExceptionalOrders.lean#L199-L234
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpJointExceptionalOrders.lean#L199-L234

import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.variableTargetHeightFailureCount_ge_reciprocal_lastCompleteShell
    {X h : ℕ} (hX : 4 ≤ X)
    {U : ℝ} (hU : 1 ≤ U)
    (hlog : Real.log U ≤
      reciprocalMaximumEpsilon * (h : ℝ) * Real.log 3)
    {f u : ℕ → ℝ}
    (hh : 0 < h) (hhM : h ≤ lastCompleteDyadicShell X)
    (htarget : ∀ n : ℕ,
      n ∈ dyadicShell (lastCompleteDyadicShell X) →
        f n < (n : ℝ) / (2 : ℝ) ^ h)
    (hu : ∀ n : ℕ,
      n ∈ dyadicShell (lastCompleteDyadicShell X) → u n ≤ U) :
    ((1 / 4) * (2 / (3 * U)) *
        (1 - reciprocalMaximumConstant / (h : ℝ))) * (X : ℝ) ≤
      variableTargetHeightFailureCount f u X := by sorry
