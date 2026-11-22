-- Prove2me | Theorems.Thm_DeciSigma1_Words_retainedCount_zero
-- name    : DeciSigma1.Words.retainedCount_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:42:06.5278+00:00
-- url     : https://prove2.me/theorems/a40c8984-23b2-46e3-952e-34e49e851779
-- title:
--   Words: retained Count zero
-- statement:
--   The Words construction uses the retained Count zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L69-L69
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L69-L69

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

theorem DeciSigma1.Words.retainedCount_zero : retainedCount D 0 = 0 := by sorry
