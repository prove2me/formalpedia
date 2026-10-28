-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_binaryTapeReadRightProgram_correct
-- name    : CountingMatroid.Bridge.binaryTapeReadRightProgram_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T19:28:04.159839+00:00
-- url     : https://prove2.me/theorems/479fd65b-069a-4e70-b494-4c4acac76617
-- title:
--   The register program reads the decoded tape head
-- statement:
--   The fixed register program reads the current cell from the right stack of a two-stack binary tape. It reports the head bit in control, preserves the decoded tape and both stacks, makes no oracle calls, and its bit-operation increase equals its instruction count.
-- source:
--   Split on the finite right stack. An empty stack takes the blank branch; a nonempty stack reads its head, restores the popped bit, and enters the branch encoding that symbol. The head-relative decoder and both stack registers are therefore unchanged.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_BinaryTapeSemantics
import Definitions.Def_CountingMatroid_Bridge_BinaryTapeReadRight

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem CountingMatroid.Bridge.binaryTapeReadRightProgram_correct {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 1 5)
    (left right : List Bool) (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = left) (h7 : c.registers 7 = right) :
    ∃ t : ℕ,
      let out := execution binaryTapeReadRightProgram O c bits t
      out.control.val = (if right.head? = some true then 5
        else if right.head? = some false then 4 else 1) ∧
      binaryTapeAt (out.registers 6) (out.registers 7) (.right 0) =
        binaryTapeAt left right (.right 0) ∧
      out.registers 6 = left ∧ out.registers 7 = right ∧
      out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + t := by
  sorry
