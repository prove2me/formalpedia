-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_spec
-- name    : DeciSigma1.Readers.StructuralReader.firstRejection_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:28.046058+00:00
-- url     : https://prove2.me/theorems/40f5b558-fcdc-4f0b-a733-4f36fc92d39b
-- title:
--   Structural Reader: first Rejection spec
-- statement:
--   The Structural Reader construction uses the first Rejection spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L511-L525
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L511-L525

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

theorem DeciSigma1.Readers.StructuralReader.firstRejection_spec {W : Fin k → List α} {i : Fin k} (h : M.Eligible W i) :
    M.firstRejection W i ≤ (W i).length ∧ M.rejected (M.runPrefix W i (M.firstRejection W i)) =
        true ∧
      ∀ a < M.firstRejection W i, M.rejected (M.runPrefix W i a) = false := by sorry
