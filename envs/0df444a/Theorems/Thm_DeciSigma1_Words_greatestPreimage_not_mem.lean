-- Prove2me | Theorems.Thm_DeciSigma1_Words_greatestPreimage_not_mem
-- name    : DeciSigma1.Words.greatestPreimage_not_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:58.987801+00:00
-- url     : https://prove2.me/theorems/8fe4c21c-8e1a-4aa6-aab3-b1a0efc0b509
-- title:
--   Words: greatest Preimage not mem
-- statement:
--   The greatest preimage of a cut is a retained position.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L255-L259
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L255-L259

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

theorem DeciSigma1.Words.greatestPreimage_not_mem (a : ℕ) : greatestPreimage D a ∉ D := by sorry
