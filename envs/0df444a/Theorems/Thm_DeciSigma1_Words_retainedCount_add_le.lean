-- Prove2me | Theorems.Thm_DeciSigma1_Words_retainedCount_add_le
-- name    : DeciSigma1.Words.retainedCount_add_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:48:29.047144+00:00
-- url     : https://prove2.me/theorems/6f20cdc6-515c-4604-a868-1d342d9bfeca
-- title:
--   Words: retained Count add le
-- statement:
--   The cut map increases by at most one at each position.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L114-L119
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Words/Deletion.lean#L114-L119

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

theorem DeciSigma1.Words.retainedCount_add_le (a n : ℕ) : retainedCount D (a + n) ≤ retainedCount D a + n := by sorry
