-- Prove2me | Theorems.Thm_DeciSigma1_Words_greatestPreimage_empty
-- name    : DeciSigma1.Words.greatestPreimage_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:10.049199+00:00
-- url     : https://prove2.me/theorems/b46c9fc9-6d83-4390-a672-d239bb409b9f
-- title:
--   Words: greatest Preimage empty
-- statement:
--   The Words construction uses the greatest Preimage empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L271-L272
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L271-L272

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

theorem DeciSigma1.Words.greatestPreimage_empty (a : ℕ) : greatestPreimage ∅ a = a := by sorry
