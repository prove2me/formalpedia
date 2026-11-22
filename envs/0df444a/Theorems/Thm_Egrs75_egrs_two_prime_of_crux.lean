-- Prove2me | Theorems.Thm_Egrs75_egrs_two_prime_of_crux
-- name    : Egrs75.egrs_two_prime_of_crux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-21T17:26:40.679021+00:00
-- url     : https://prove2.me/theorems/182c929e-054f-477b-b393-1d38087e8b7a
-- title:
--   Egrs75: egrs two prime of crux
-- statement:
--   **EGRS two-prime target, conditional on the crux.** Given the crux
--   (`EgrsCrux p q`, i.e. `A_p ∩ A_q` infinite) for distinct odd primes `p q`, there
--   are infinitely many `n` with `p ∤ C(2n,n)` and `q ∤ C(2n,n)`.
--
--   This proof is SORRY-FREE: it uses ONLY the kernel-clean single-base bridge
--   `not_dvd_centralBinom_iff_lowDigits` to rewrite the divisibility set as the joint
--   low-digit set, then applies the crux hypothesis. `#print axioms` below confirms
--   propext / Classical.choice / Quot.sound only (NO sorryAx) for this lemma.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Reduction.lean#L98-L108
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Egrs75/Reduction.lean#L98-L108

module
public import Definitions.Def_LeanPool_Egrs75_Defs
public import Mathlib.Data.Finite.Defs
public import Mathlib.Data.Finset.Attr
public import Definitions.Def_LeanPool_Egrs75_Reduction
set_option autoImplicit true
@[expose] public section
public section
open Egrs75
open Nat

theorem Egrs75.egrs_two_prime_of_crux {p q : ℕ} (hp : p.Prime) (hq : q.Prime)
    (hpo : Odd p) (hqo : Odd q) (hcrux : EgrsCrux p q) :
    {n : ℕ | ¬ p ∣ Nat.centralBinom n ∧ ¬ q ∣ Nat.centralBinom n}.Infinite := by sorry
