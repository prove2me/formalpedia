-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_le
-- name    : DeciSigma1.Readers.StructuralReader.firstRejection_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:44:41.386998+00:00
-- url     : https://prove2.me/theorems/660a82c0-e921-4bd2-ac6e-e9e8008a6979
-- title:
--   Structural Reader: first Rejection le
-- statement:
--   The Structural Reader construction uses the first Rejection le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L527-L528
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L527-L528

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

theorem DeciSigma1.Readers.StructuralReader.firstRejection_le {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) :
    M.firstRejection W i ≤ (W i).length := by sorry
