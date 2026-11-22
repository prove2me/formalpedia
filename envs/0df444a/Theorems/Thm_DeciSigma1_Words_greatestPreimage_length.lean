-- Prove2me | Theorems.Thm_DeciSigma1_Words_greatestPreimage_length
-- name    : DeciSigma1.Words.greatestPreimage_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:47:02.521845+00:00
-- url     : https://prove2.me/theorems/e45c1236-13a0-4b8a-92c1-cfc71e7d0660
-- title:
--   Words: greatest Preimage length
-- statement:
--   If the end of `w` is not deleted, it is the greatest preimage of the end of the edited
--   word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L298-L300
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L298-L300

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

theorem DeciSigma1.Words.greatestPreimage_length (w : List α) (hD : w.length ∉ D) :
    greatestPreimage D (deletePositions w D).length = w.length := by sorry
