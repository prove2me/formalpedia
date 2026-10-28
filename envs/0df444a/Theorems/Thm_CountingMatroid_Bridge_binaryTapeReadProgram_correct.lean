-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_binaryTapeReadProgram_correct
-- name    : CountingMatroid.Bridge.binaryTapeReadProgram_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T18:44:38.009119+00:00
-- url     : https://prove2.me/theorems/16bb533b-70b9-42da-9502-15a9276a34cd
-- title:
--   The binary tape head read preserves its exact representation
-- statement:
--   A fixed binary-register program reads the current tape bit from a stack representation. It distinguishes blank, false, and true cells in control, restores the exact stack, leaves output unchanged, makes no oracle calls, and records the exact instruction count as bit operations.
-- source:
--   The proof follows the three possible head cases. For a blank stack the pop instruction enters the blank state. For an explicit bit it pops that bit, then pushes the same bit back and enters its distinct return state. Each instruction increments the bit-operation counter once and none changes oracle calls.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_BinaryTapeRead

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem CountingMatroid.Bridge.binaryTapeReadProgram_correct {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 0 5) (xs : List Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = xs) :
    ∃ t : ℕ,
      let out := execution binaryTapeReadProgram O c bits t
      (out.control.val =
        (if xs.head? = some true then 5 else if xs.head? = some false then 4 else 1)) ∧
      out.registers 6 = xs ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + t := by
  sorry
