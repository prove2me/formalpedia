-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Table_mem_visitedStates
-- name    : DeciSigma1.Readers.Table.mem_visitedStates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:35.416748+00:00
-- url     : https://prove2.me/theorems/2d537323-35a8-432c-bd5e-b7f9f9bd4a0b
-- title:
--   Table: mem visited States
-- statement:
--   The Table construction uses the mem visited States property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L160-L162
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L160-L162

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
open DeciSigma1.Readers.Table
variable (T : Table α S k)
variable {T}

theorem DeciSigma1.Readers.Table.mem_visitedStates [DecidableEq S] {W : Fin k → List α} {i : Fin k} {s : S} :
    s ∈ T.visitedStates W i ↔ ∃ a ≤ (W i).length, T.runPrefix W i a = s := by sorry
