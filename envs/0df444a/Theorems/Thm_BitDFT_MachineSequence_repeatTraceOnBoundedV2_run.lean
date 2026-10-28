-- Prove2me | Theorems.Thm_BitDFT_MachineSequence_repeatTraceOnBoundedV2_run
-- name    : BitDFT.MachineSequence.repeatTraceOnBoundedV2_run
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T23:00:09.690744+00:00
-- url     : https://prove2.me/theorems/fb6a054c-4b83-40b6-8515-be55af68d2ad
-- title:
--   A complete repeated run includes its final body and blank test
-- statement:
--   Let a finite-state body controller process records on a designated source tape, and suppose each body run costs at most B steps. If the final body run advances the source onto a blank sentinel, the repeated machine executes every body and the terminating blank test. Its exact final configuration is the stated halt configuration, and for r processed records the total number of transitions is at most r(B+1).
-- source:
--   Exact-run and runtime theorem for the corrected bounded trace, including the final body execution that reaches the blank sentinel.

import Definitions.Def_BitDFT_RepeatTraceOnBoundedV2
import Mathlib.Tactic
set_option autoImplicit false
set_option maxHeartbeats 0
open IntMul BitDFT.MachineSequence

theorem BitDFT.MachineSequence.repeatTraceOnBoundedV2_run {M : MultitapeTM} (source : Fin M.k)
    (P : Controller M) {B t : ℕ} {c : P.machine.Cfg}
    {final : (repeatMachineOn source P).Cfg}
    (h : RepeatTraceOnBoundedV2 source P B t c final) :
    (repeatMachineOn source P).step^[t] (repeatBodyCfgOn source c) = final ∧
      t ≤ repeatTraceOnBoundedV2Rounds h * (B + 1) := by sorry
