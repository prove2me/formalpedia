-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_setFinsetQueryProgram_correct
-- name    : CountingMatroid.Bridge.setFinsetQueryProgram_correct
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T16:41:43.672173+00:00
-- url     : https://prove2.me/theorems/d135a9dc-897e-4e25-824d-fc4f18c91ff4
-- title:
--   The updated finite set is queried with exact independence semantics
-- statement:
--   Starting with the canonical membership vector of I and unary index i, the fixed program writes true or false at i to form S = insert i I or I.erase i, then makes one exact independence-oracle query for the requested matroid. It branches to state 11 exactly when S is independent and to state 10 otherwise. It leaves the canonical vector of S in register 6, clears scratch registers 7 and 8, produces no machine output, makes exactly one oracle call, and uses (5i+5)+(2n+1) bit operations.
-- source:
--   Composition of the accepted indexed setter and its Finset-semantics theorem with the target machine query instruction. ExactOracles identifies the queried vector predicate with matroid independence; the proof also establishes exact register contents, oracle count, and bit-operation charge.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_SetFinsetQueryProgram
import Theorems.Thm_CountingMatroid_Bridge_setMembershipBitProgram_finset_correct

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS
open scoped Classical

theorem CountingMatroid.Bridge.setFinsetQueryProgram_correct {n : ℕ}
    (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n)) (i : Fin n)
    (value which : Bool) (O : IndependenceOracle n)
    (hExact : ExactOracles M₁ M₂ O) (bits : ℕ → Bool)
    (c : MachineConfig 2 11)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = finsetMembershipBits I)
    (h7 : c.registers 7 = List.replicate i.val true)
    (h8 : c.registers 8 = []) :
    let S := if value then insert i I else I.erase i
    let out := execution (setFinsetQueryProgram value which) O c bits
      (5 * i.val + 6)
    out.control.val = (if (if which then M₂ else M₁).Indep (S : Set (Fin n)) then 11 else 10) ∧
      out.registers 6 = finsetMembershipBits S ∧
      out.registers 7 = [] ∧ out.registers 8 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls + 1 ∧
      out.bitOperations = c.bitOperations + (5 * i.val + 5) + (2 * n + 1) := by
  sorry
