-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_binaryTapeMoveLeftProgram_correct
-- name    : CountingMatroid.Bridge.binaryTapeMoveLeftProgram_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T18:58:00.802977+00:00
-- url     : https://prove2.me/theorems/26f8dc49-8500-4dc1-9549-b4c1b11dd46d
-- title:
--   A fixed machine moves its binary tape head left exactly
-- statement:
--   For left and right stack encodings of a binary tape, a fixed program moves the head one cell to the left. It removes the previous left cell, places it before the old current cell on the right stack, treats absent cells as blank, preserves output, makes no oracle calls, and uses exactly four bit operations.
-- source:
--   The machine pops the old current cell and then the previous left cell. The control state retains both bits while two pushes prepend the old current cell and then the new current cell to the right stack. Empty stacks supply false, so the same four instructions handle missing cells.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_BinaryTapeMoveLeft

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem CountingMatroid.Bridge.binaryTapeMoveLeftProgram_correct {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 0 17)
    (left right : List Bool) (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = left) (h7 : c.registers 7 = right) :
    let out := execution binaryTapeMoveLeftProgram O c bits 4
    out.control.val = (if right.headD false then
        (if left.headD false then 15 else 14)
      else if left.headD false then 13 else 12) ∧
      out.registers 6 = left.drop 1 ∧
      out.registers 7 = (left.headD false) :: (right.headD false) :: (right.drop 1) ∧
      out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + 4 := by
  sorry
