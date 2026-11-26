-- Prove2me | Theorems.Thm_FirstPassageLinearTransport_X_lt_four_mul_pow_lastCompleteDyadicShell
-- name    : FirstPassageLinearTransport.X_lt_four_mul_pow_lastCompleteDyadicShell
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T12:55:35.949865+00:00
-- url     : https://prove2.me/theorems/1fb588cc-5b15-445d-abf4-93aac8b8158f
-- title:
--   First Passage Linear Transport: X lt four mul pow last Complete Dyadic Shell
-- statement:
--   The First Passage Linear Transport construction uses the X lt four mul pow last Complete Dyadic Shell property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpJointExceptionalOrders.lean#L146-L162
-- source:
--   https://github.com/shaikidris/FirstPassageLinearTransport-Palomar/blob/39a6ba1940a1523e7491e32889f61afd235bb8df/FirstPassageLinearTransport/SharpJointExceptionalOrders.lean#L146-L162

import Definitions.Def_FirstPassageLinearTransport_ReciprocalHeightObstruction
import Definitions.Def_FirstPassageLinearTransport_SharpJointExceptionalOrders
set_option autoImplicit true
open FirstPassageLinearTransport
open Filter
open scoped BigOperators Real Topology
noncomputable section

theorem FirstPassageLinearTransport.X_lt_four_mul_pow_lastCompleteDyadicShell
    {X : ℕ} (hX : 4 ≤ X) :
    X < 4 * 2 ^ lastCompleteDyadicShell X := by sorry
