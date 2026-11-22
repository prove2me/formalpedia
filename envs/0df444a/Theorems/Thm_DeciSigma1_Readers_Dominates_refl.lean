-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Dominates_refl
-- name    : DeciSigma1.Readers.Dominates.refl
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:56.686039+00:00
-- url     : https://prove2.me/theorems/2afc5b92-3c2a-43d0-a2cc-d749cf4ac753
-- title:
--   Dominates: refl
-- statement:
--   The Dominates construction uses the refl property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L265-L266
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L265-L266

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Automata_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Pigeonhole
public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Tactic.Linarith
public import Mathlib.Data.Finset.Prod
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Readers
open DeciSigma1.Automata
variable {α S : Type} {k : ℕ}
open Table
variable [DecidableEq α] [DecidableEq S]
variable {T : Table α S k} {U V W : Fin k → List α}

theorem DeciSigma1.Readers.Dominates.refl (T : Table α S k) (W : Fin k → List α) : Dominates T W W := by sorry
