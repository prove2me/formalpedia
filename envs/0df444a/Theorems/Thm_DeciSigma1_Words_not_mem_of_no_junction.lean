-- Prove2me | Theorems.Thm_DeciSigma1_Words_not_mem_of_no_junction
-- name    : DeciSigma1.Words.not_mem_of_no_junction
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:23.062401+00:00
-- url     : https://prove2.me/theorems/19eedda1-767f-4c1e-96f3-0e0445169108
-- title:
--   Words: not mem of no junction
-- statement:
--   If no junction lies strictly between the cuts `a` and `a + n` of the edited word, the `n`
--   positions from the greatest preimage of `a` are retained.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L403-L412
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L403-L412

module
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Tactic.Ring.RingNF
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Words
open DeciSigma1.Readers
variable {α S : Type} {k : ℕ}
variable {D : Finset ℕ}

theorem DeciSigma1.Words.not_mem_of_no_junction {a n : ℕ}
    (hJ : ∀ p ∈ D, ¬ (a < retainedCount D p ∧ retainedCount D p < a + n)) :
    ∀ i < n, greatestPreimage D a + i ∉ D := by sorry
