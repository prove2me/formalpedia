-- Prove2me | Theorems.Thm_DeciSigma1_Words_greatestPreimage_mono
-- name    : DeciSigma1.Words.greatestPreimage_mono
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:20.55562+00:00
-- url     : https://prove2.me/theorems/97102746-1e8c-41e7-81b6-fd8e1fb5d286
-- title:
--   Words: greatest Preimage mono
-- statement:
--   The Words construction uses the greatest Preimage mono property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L268-L269
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L268-L269

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

theorem DeciSigma1.Words.greatestPreimage_mono {a b : ℕ} (h : a ≤ b) : greatestPreimage D a ≤ greatestPreimage D b := by sorry
