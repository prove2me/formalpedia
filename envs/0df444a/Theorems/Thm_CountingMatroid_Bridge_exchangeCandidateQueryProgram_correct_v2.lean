-- Prove2me | Theorems.Thm_CountingMatroid_Bridge_exchangeCandidateQueryProgram_correct_v2
-- name    : CountingMatroid.Bridge.exchangeCandidateQueryProgram_correct_v2
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-10-25T18:23:39.94546+00:00
-- url     : https://prove2.me/theorems/9138effd-ba88-40ed-ac1d-ab7c82dca6e9
-- title:
--   The directed exchange candidate is built and queried exactly
-- statement:
--   Given the canonical membership vector of I and unary indices u and v, a fixed program constructs insert(v, I.erase(u)) and queries the selected matroid oracle. Its branch is exactly whether that candidate is independent. It preserves the canonical candidate vector, clears scratch registers 7 through 9, leaves output empty, makes exactly one oracle call, and uses 5u+7v+12 preprocessing bit operations plus 2n+1 query bit operations.
-- source:
--   Compose the two accepted indexed-setter simulations with the exact-oracle query instruction. The proof explicitly copies the second unary index, proves the exchange vector register invariant and exact preprocessing cost, then uses ExactOracles to identify the query branch with matroid independence.

import Mathlib
import Definitions.Def_CommonBasesFPRAS
import Definitions.Def_CountingMatroid_Bridge_ExchangeCandidateQuery
import Theorems.Thm_CountingMatroid_Bridge_setMembershipBitProgram_finset_correct

set_option autoImplicit false
set_option maxHeartbeats 800000
open OAI.CommonBasesFPRAS
open scoped Classical

theorem CountingMatroid.Bridge.exchangeCandidateQueryProgram_correct_v2 {n : ℕ}
    (M₁ M₂ : Matroid (Fin n)) (I : Finset (Fin n)) (u v : Fin n)
    (which : Bool) (O : IndependenceOracle n)
    (hExact : ExactOracles M₁ M₂ O) (bits : ℕ → Bool)
    (c : MachineConfig 2 27)
    (hc : c.control.val = 0) (ho : c.output = none)
    (h6 : c.registers 6 = finsetMembershipBits I)
    (h7 : c.registers 7 = List.replicate u.val true)
    (h8 : c.registers 8 = []) (h9 : c.registers 9 = List.replicate v.val true) :
    let S := insert v (I.erase u)
    let t := 5 * u.val + 7 * v.val + 12
    let out := execution (exchangeCandidateQueryProgram which) O c bits (t + 1)
    out.control.val = (if (if which then M₂ else M₁).Indep (S : Set (Fin n)) then 11 else 10) ∧
      out.registers 6 = finsetMembershipBits S ∧ out.registers 7 = [] ∧
      out.registers 8 = [] ∧ out.registers 9 = [] ∧ out.output = none ∧
      out.oracleCalls = c.oracleCalls + 1 ∧
      out.bitOperations = c.bitOperations + t + (2 * n + 1) := by
  sorry
