-- Prove2me | Theorems.Thm_DeciSigma1_Words_greatestPreimage_union_Ico
-- name    : DeciSigma1.Words.greatestPreimage_union_Ico
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:26.338475+00:00
-- url     : https://prove2.me/theorems/5bc56034-8306-4010-9b42-3df4db3fdf39
-- title:
--   Words: greatest Preimage union Ico
-- statement:
--   The Words construction uses the greatest Preimage union Ico property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L466-L484
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L466-L484

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
variable {c δ : ℕ}

theorem DeciSigma1.Words.greatestPreimage_union_Ico (hD : ∀ p ∈ D, p < c) (a : ℕ) :
    greatestPreimage (D ∪ Finset.Ico c (c + δ)) a =
      if greatestPreimage D a < c then greatestPreimage D a else greatestPreimage D a + δ := by sorry
