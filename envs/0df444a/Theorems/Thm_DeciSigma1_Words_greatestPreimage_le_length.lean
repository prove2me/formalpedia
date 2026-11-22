-- Prove2me | Theorems.Thm_DeciSigma1_Words_greatestPreimage_le_length
-- name    : DeciSigma1.Words.greatestPreimage_le_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:32.775118+00:00
-- url     : https://prove2.me/theorems/084263d2-af99-4cbb-ab1e-1e1af31010a9
-- title:
--   Words: greatest Preimage le length
-- statement:
--   The Words construction uses the greatest Preimage le length property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L302-L304
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L302-L304

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

theorem DeciSigma1.Words.greatestPreimage_le_length (w : List α) (hD : w.length ∉ D) {a : ℕ}
    (ha : a ≤ (deletePositions w D).length) : greatestPreimage D a ≤ w.length := by sorry
