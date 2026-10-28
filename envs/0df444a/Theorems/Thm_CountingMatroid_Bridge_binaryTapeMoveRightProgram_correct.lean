-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_binaryTapeMoveRightProgram_correct
-- name    : CountingMatroid.Bridge.binaryTapeMoveRightProgram_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T18:51:17.512927+00:00
-- url     : https://prove2.me/theorems/611db96e-70ad-47a9-8a52-9c304e63e2c8
-- title:
--   A fixed machine moves its binary tape head right exactly
-- statement:
--   For left and right stack encodings of a binary tape, a fixed program moves the head one cell to the right. It pushes the old head bit onto the left stack, leaves the remaining suffix on the right, treats an absent old head cell as blank, preserves output, makes no oracle calls, and uses exactly two bit operations.
-- source:
--   Case split on the current right stack and head bit. The machine first pops the current cell (or takes the empty branch), then pushes the represented old cell onto the left stack. The right suffix and both counters follow directly from the two instructions.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_BinaryTapeMoveRight

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem CountingMatroid.Bridge.binaryTapeMoveRightProgram_correct {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 0 6)
    (left right : List Bool) (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = left) (h7 : c.registers 7 = right) :
    let out := execution binaryTapeMoveRightProgram O c bits 2
    out.control.val = (if right.head? = some true then 6 else 5) ∧
      out.registers 6 = (right.headD false) :: left ∧
      out.registers 7 = right.drop 1 ∧
      out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + 2 := by
  sorry
