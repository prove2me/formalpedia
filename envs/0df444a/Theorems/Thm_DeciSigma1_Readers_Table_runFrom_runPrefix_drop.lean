-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Table_runFrom_runPrefix_drop
-- name    : DeciSigma1.Readers.Table.runFrom_runPrefix_drop
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:20.198716+00:00
-- url     : https://prove2.me/theorems/5ac93401-fe1f-4c5e-919c-2897435734f1
-- title:
--   Table: run From run Prefix drop
-- statement:
--   Reading the whole suffix from cut `a` reaches the endpoint.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L152-L158
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L152-L158

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

theorem DeciSigma1.Readers.Table.runFrom_runPrefix_drop (W : Fin k → List α) (i : Fin k) (a : ℕ) :
    runFrom T.step (T.runPrefix W i a) ((W i).drop a) = T.endState W i := by sorry
