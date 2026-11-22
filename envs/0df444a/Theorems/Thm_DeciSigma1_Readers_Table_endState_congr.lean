-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Table_endState_congr
-- name    : DeciSigma1.Readers.Table.endState_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:21.928605+00:00
-- url     : https://prove2.me/theorems/b67a845e-56c4-44e0-921c-f6ec1a1a1612
-- title:
--   Table: end State congr
-- statement:
--   The endpoint of a coordinate depends only on its word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L199-L201
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L199-L201

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

theorem DeciSigma1.Readers.Table.endState_congr {U W : Fin k → List α} {i : Fin k} (h : U i = W i) :
    T.endState U i = T.endState W i := by sorry
