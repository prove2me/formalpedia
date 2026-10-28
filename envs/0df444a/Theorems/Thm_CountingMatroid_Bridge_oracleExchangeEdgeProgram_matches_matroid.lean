-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_oracleExchangeEdgeProgram_matches_matroid
-- name    : CountingMatroid.Bridge.oracleExchangeEdgeProgram_matches_matroid
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T15:49:09.487097+00:00
-- url     : https://prove2.me/theorems/69dcb6ff-f901-4f59-81a8-87f5647de3d1
-- title:
--   The oracle machine computes the matroid exchange-edge predicate
-- statement:
--   Let M₁ and M₂ be matroids on [n], let I be a subset of [n], and let u,v be ground-set elements. Assume the two membership guards and the two candidate-set characteristic vectors encode the directed exchange tests. If the two independence oracles answer exactly according to M₁ and M₂, then the fixed four-step oracle program reaches its accepting state exactly when u → v is an exchange edge in the matroid-intersection graph. It makes two oracle calls, preserves both candidate vectors, clears the guards, and uses 4n+4 bit operations.
-- source:
--   A kernel-checked Lean 4.33.1 bridge from the already verified fixed oracle program to Mathlib matroid independence. Submitted as a reusable dependency of the existing mission; no Arlib dependency.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_ExchangeEdgeInterface
import Theorems.Thm_CountingMatroid_Bridge_oracleExchangeEdgeProgram_correct

set_option autoImplicit false
set_option maxHeartbeats 800000

open OAI.CommonBasesFPRAS

theorem CountingMatroid.Bridge.oracleExchangeEdgeProgram_matches_matroid {n : ℕ}
    (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n)) (u v : Fin n)
    (O : OAI.CommonBasesFPRAS.IndependenceOracle n) (bits : ℕ → Bool)
    (c : MachineConfig 2 16)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = [decide (u ∈ I ∧ v ∉ I)])
    (h7 : c.registers 7 = [decide (u ∉ I ∧ v ∈ I)])
    (h8 : c.registers 8 = List.ofFn (fun j : Fin n => decide (j ∈ insert v (I.erase u))))
    (h9 : c.registers 9 = List.ofFn (fun j : Fin n => decide (j ∈ insert u (I.erase v))))
    (hExact : OAI.CommonBasesFPRAS.ExactOracles M₁ M₂ O) :
    let out := execution CountingMatroid.Bridge.oracleExchangeEdgeProgram O c bits 4
    out.control.val = (if CountingMatroid.Bridge.matroidExchangeEdge M₁ M₂ I u v then 12 else 10) ∧
    out.registers 6 = [] ∧ out.registers 7 = [] ∧
    out.registers 8 = List.ofFn (fun j : Fin n => decide (j ∈ insert v (I.erase u))) ∧
    out.registers 9 = List.ofFn (fun j : Fin n => decide (j ∈ insert u (I.erase v))) ∧
    out.output = none ∧ out.oracleCalls = c.oracleCalls + 2 ∧
    out.bitOperations = c.bitOperations + (4 * n + 4) := by
  sorry
