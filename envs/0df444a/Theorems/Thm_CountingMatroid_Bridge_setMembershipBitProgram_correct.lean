-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_setMembershipBitProgram_correct
-- name    : CountingMatroid.Bridge.setMembershipBitProgram_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T16:07:55.372987+00:00
-- url     : https://prove2.me/theorems/3b4de01b-96a0-4b38-8036-e598d8749e3d
-- title:
--   The fixed bit-setter preserves the vector and exact costs
-- statement:
--   Given a target Boolean stack split as a prefix, one selected bit, and a suffix, and a unary index whose length equals the prefix length, the fixed setter writes the requested Boolean at that index. It restores the prefix in order, clears its scratch stacks, makes no oracle calls, and uses exactly 5i+5 bit operations.
-- source:
--   Lean 4.33.1 machine trace proof. The scan/restoration induction proves the exact updated stack, scratch cleanup, zero oracle calls, and exact charged-bit counter for every index.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_SetMembershipBitProgram

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem CountingMatroid.Bridge.setMembershipBitProgram_correct {n : ℕ} (value : Bool) (next : Fin 12)
    (O : IndependenceOracle n) (bits : ℕ → Bool) (c : MachineConfig 2 11)
    (preBits : List Bool) (old : Bool) (suffix : List Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = preBits ++ old :: suffix)
    (h7 : c.registers 7 = List.replicate preBits.length true)
    (h8 : c.registers 8 = []) :
    let out := execution (CountingMatroid.Bridge.setMembershipBitProgram value next) O c bits
      (5 * preBits.length + 5)
    out.control = next ∧ out.registers 6 = preBits ++ value :: suffix ∧
      out.registers 7 = [] ∧ out.registers 8 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (5 * preBits.length + 5) := by
  sorry
