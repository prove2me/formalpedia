-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Table_pair_mem_channel
-- name    : DeciSigma1.Readers.Table.pair_mem_channel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:14.734096+00:00
-- url     : https://prove2.me/theorems/08f5594d-7a03-42c8-95a0-f197b0f877e2
-- title:
--   Table: pair mem channel
-- statement:
--   The Table construction uses the pair mem channel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L188-L192
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L188-L192

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

theorem DeciSigma1.Readers.Table.pair_mem_channel [DecidableEq α] [DecidableEq S] {W : Fin k → List α} {i j : Fin k}
    {a b : ℕ} (ha : a ≤ (W i).length) (hb : b ≤ (W j).length)
    (h : (W j).drop b <+: (W i).drop a) : (T.runPrefix W i a, T.runPrefix W j b) ∈
        T.channel W i j := by sorry
