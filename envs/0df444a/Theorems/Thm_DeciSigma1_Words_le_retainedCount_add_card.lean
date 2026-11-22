-- Prove2me | Theorems.Thm_DeciSigma1_Words_le_retainedCount_add_card
-- name    : DeciSigma1.Words.le_retainedCount_add_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:02.456814+00:00
-- url     : https://prove2.me/theorems/19734c3c-b78f-4547-8fc5-ef1b4b7033ea
-- title:
--   Words: le retained Count add card
-- statement:
--   At most `|D|` positions are deleted below any cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L152-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L152-L158

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

theorem DeciSigma1.Words.le_retainedCount_add_card (a : ℕ) : a ≤ retainedCount D a + D.card := by sorry
