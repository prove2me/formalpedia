-- Prove2me | Theorems.Thm_Champernowne_card_allWords
-- name    : Champernowne.card_allWords
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-20T21:37:24.623003+00:00
-- url     : https://prove2.me/theorems/9f3abde4-98d1-4aeb-88f1-bbd81efe7704
-- title:
--   Champernowne: card all Words
-- statement:
--   The Champernowne construction uses the card all Words property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L141-L162
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/Champernowne/Count.lean#L141-L162

module
public import Definitions.Def_LeanPool_Champernowne_Defs
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.Algebra.BigOperators.Intervals
public import Mathlib.Data.Finset.Powerset
public import Definitions.Def_LeanPool_Champernowne_Count
set_option autoImplicit true
@[expose] public section
public section
open Champernowne

theorem Champernowne.card_allWords (b k : ℕ) : (allWords b k).card = b ^ k := by sorry
