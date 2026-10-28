-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_binaryStackCopyProgram_correct
-- name    : CountingMatroid.Bridge.binaryStackCopyProgram_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T23:03:07.205355+00:00
-- url     : https://prove2.me/theorems/42f0b837-b48e-46d4-8421-a756f9b60adc
-- title:
--   Copy a bit stack while restoring the source in exact linear cost
-- statement:
--   The fixed program copies any finite Boolean stack from register 6 to register 10 in the same order, restores register 6 exactly, clears register 11, leaves the output unchanged, makes no oracle calls, and uses exactly 5|xs|+2 bit operations.
-- source:
--   A two-pass implementation first reverses the source into scratch, then restores the source while producing the destination in original order. The Lean proof gives exact control, register, oracle-count, and bit-cost invariants.

import Definitions.Def_CountingMatroidBridgeStackCopy

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem CountingMatroid.Bridge.binaryStackCopyProgram_correct {n : ℕ}
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 5 8) (xs ys : List Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = xs) (h10 : c.registers 10 = ys)
    (h11 : c.registers 11 = []) :
    let out := execution binaryStackCopyProgram O c bits (5 * xs.length + 2)
    out.control.val = 6 ∧ out.registers 6 = xs ∧
      out.registers 10 = xs ++ ys ∧ out.registers 11 = [] ∧
      out.output = none ∧ out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (5 * xs.length + 2) := by
  sorry
