-- Prove2me | Theorems.Thm_DeciSigma1_Readers_exists_isMinimalFresh_freshDominates
-- name    : DeciSigma1.Readers.exists_isMinimalFresh_freshDominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:31.57847+00:00
-- url     : https://prove2.me/theorems/cbf8306c-9b8a-4b62-a665-dc92feeea135
-- title:
--   Readers: exists is Minimal Fresh fresh Dominates
-- statement:
--   Every fresh tuple has a minimal fresh dominator: a fresh dominator of least total length
--   is minimal, since fresh domination is transitive.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L297-L305
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L297-L305

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

theorem DeciSigma1.Readers.exists_isMinimalFresh_freshDominates (hW : ∀ i, T.Fresh W i) :
    ∃ U, FreshDominates T U W ∧ IsMinimalFresh T U := by sorry
