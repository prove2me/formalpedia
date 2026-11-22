-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_runPrefix_ne
-- name    : DeciSigma1.Readers.StructuralReader.Eligible.runPrefix_ne
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:11.403041+00:00
-- url     : https://prove2.me/theorems/b526b51b-6cf7-4be3-a78f-add9fc4d1a6e
-- title:
--   Eligible: run Prefix ne
-- statement:
--   The Eligible construction uses the run Prefix ne property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L499-L503
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L499-L503

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
open DeciSigma1.Readers.StructuralReader
variable (M : StructuralReader α S k)
variable {M}

theorem DeciSigma1.Readers.StructuralReader.Eligible.runPrefix_ne {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) (a : ℕ) :
    M.runPrefix W i a ≠ M.dead := by sorry
