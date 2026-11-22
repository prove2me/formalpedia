-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Table_mem_pathChannel
-- name    : DeciSigma1.Readers.Table.mem_pathChannel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:27.539893+00:00
-- url     : https://prove2.me/theorems/fb9c5794-0ca9-47db-bded-b771836644be
-- title:
--   Table: mem path Channel
-- statement:
--   The Table construction uses the mem path Channel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L172-L181
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L172-L181

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

theorem DeciSigma1.Readers.Table.mem_pathChannel [DecidableEq α] [DecidableEq S] {p q : S} {x y : List α} {pq : S × S} :
    pq ∈ T.pathChannel p x q y ↔ ∃ a ≤ x.length, ∃ b ≤ y.length,
      y.drop b <+: x.drop a ∧ pq = (runFrom T.step p (x.take a), runFrom T.step q (y.take b)) := by sorry
