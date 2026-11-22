-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Table_channel_congr
-- name    : DeciSigma1.Readers.Table.channel_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:27.554378+00:00
-- url     : https://prove2.me/theorems/cd47f62e-d146-417a-8db8-bcbb142f6beb
-- title:
--   Table: channel congr
-- statement:
--   A channel depends only on the words of its two coordinates.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L204-L206
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L204-L206

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

theorem DeciSigma1.Readers.Table.channel_congr [DecidableEq α] [DecidableEq S] {U W : Fin k → List α} {i j : Fin k}
    (hi : U i = W i) (hj : U j = W j) : T.channel U i j = T.channel W i j := by sorry
