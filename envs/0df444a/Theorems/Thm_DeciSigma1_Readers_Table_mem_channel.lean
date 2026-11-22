-- Prove2me | Theorems.Thm_DeciSigma1_Readers_Table_mem_channel
-- name    : DeciSigma1.Readers.Table.mem_channel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:45:48.798651+00:00
-- url     : https://prove2.me/theorems/ea560332-27bd-4c02-a65d-50fecc08c53f
-- title:
--   Table: mem channel
-- statement:
--   The Table construction uses the mem channel property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L183-L186
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L183-L186

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

theorem DeciSigma1.Readers.Table.mem_channel [DecidableEq α] [DecidableEq S] {W : Fin k → List α} {i j : Fin k}
    {pq : S × S} :
    pq ∈ T.channel W i j ↔ ∃ a ≤ (W i).length, ∃ b ≤ (W j).length,
      (W j).drop b <+: (W i).drop a ∧ pq = (T.runPrefix W i a, T.runPrefix W j b) := by sorry
