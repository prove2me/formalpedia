-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_setMembershipBitProgram_finset_correct
-- name    : CountingMatroid.Bridge.setMembershipBitProgram_finset_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T16:12:58.48362+00:00
-- url     : https://prove2.me/theorems/59903d18-67c0-412a-b4f5-c08f078451aa
-- title:
--   The fixed setter constructs the canonical inserted or erased Finset vector
-- statement:
--   When register 6 initially holds the canonical membership vector of I and the unary index is i, the same fixed setter produces exactly the canonical vector of I with i inserted (for value true) or erased (for value false). All other machine registers and exact costs satisfy the generic setter contract.
-- source:
--   This dependent theorem turns the generic machine trace into concrete Finset semantics using the canonical Boolean membership encoding. It gives the exact machine-ready update needed to prepare exchange-edge oracle queries.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_SetMembershipBitProgram
import Theorems.Thm_CountingMatroid_Bridge_setMembershipBitProgram_correct

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS

theorem CountingMatroid.Bridge.setMembershipBitProgram_finset_correct {n : ℕ} (value : Bool) (next : Fin 12)
    (O : IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 11) (s : Finset (Fin n)) (i : Fin n)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = CountingMatroid.Bridge.finsetMembershipBits s)
    (h7 : c.registers 7 = List.replicate i.val true)
    (h8 : c.registers 8 = []) :
    let out := execution (CountingMatroid.Bridge.setMembershipBitProgram value next) O c bits
      (5 * i.val + 5)
    out.control = next ∧
      out.registers 6 = CountingMatroid.Bridge.finsetMembershipBits
        (if value then insert i s else s.erase i) ∧
      out.registers 7 = [] ∧ out.registers 8 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls ∧
      out.bitOperations = c.bitOperations + (5 * i.val + 5) := by
  sorry
