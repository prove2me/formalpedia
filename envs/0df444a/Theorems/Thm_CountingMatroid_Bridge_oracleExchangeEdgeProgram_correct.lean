-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_oracleExchangeEdgeProgram_correct
-- name    : CountingMatroid.Bridge.oracleExchangeEdgeProgram_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T15:18:21.824549+00:00
-- url     : https://prove2.me/theorems/af3d05ea-b22f-46fd-8a2c-91b4e034e9f8
-- title:
--   The fixed exchange-edge program makes two exact oracle calls
-- statement:
--   From an initial configuration with one-bit forward and reverse guards and two length-n query vectors, four steps perform two oracle calls, clear the guards, preserve both query vectors, and reach state 12 iff an enabled query is accepted. The exact bit-operation charge is 4n+4.
-- source:
--   Local Lean 4.33.1 kernel-checked proof for the existing counting-matroid mission. It verifies all four guard combinations and both oracle answers; it does not claim to implement the full estimator.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_OracleExchangeProgram

set_option autoImplicit false
set_option maxHeartbeats 800000

open OAI.CommonBasesFPRAS

theorem CountingMatroid.Bridge.oracleExchangeEdgeProgram_correct {n : ℕ}
    (O : OAI.CommonBasesFPRAS.IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 16) (forward reverse : Bool)
    (qForward qReverse : Fin n → Bool)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = [forward]) (h7 : c.registers 7 = [reverse])
    (h8 : c.registers 8 = List.ofFn qForward)
    (h9 : c.registers 9 = List.ofFn qReverse) :
    let out := execution CountingMatroid.Bridge.oracleExchangeEdgeProgram O c bits 4
    out.control.val = (if (forward && O false qForward) || (reverse && O true qReverse) then 12 else 10) ∧
    out.registers 6 = [] ∧ out.registers 7 = [] ∧
    out.registers 8 = List.ofFn qForward ∧ out.registers 9 = List.ofFn qReverse ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls + 2 ∧
    out.bitOperations = c.bitOperations + (4 * n + 4) := by
  sorry
