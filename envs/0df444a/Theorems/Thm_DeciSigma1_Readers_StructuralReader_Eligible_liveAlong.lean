-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_Eligible_liveAlong
-- name    : DeciSigma1.Readers.StructuralReader.Eligible.liveAlong
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:52:31.9387+00:00
-- url     : https://prove2.me/theorems/1d521a95-c7ef-4850-a37b-e4e3bb1624e4
-- title:
--   Eligible: live Along
-- statement:
--   The Eligible construction uses the live Along property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L505-L509
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L505-L509

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

theorem DeciSigma1.Readers.StructuralReader.Eligible.liveAlong {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) (a : ℕ) :
    M.LiveAlong (M.runPrefix W i a) ((W i).drop a) := by sorry
