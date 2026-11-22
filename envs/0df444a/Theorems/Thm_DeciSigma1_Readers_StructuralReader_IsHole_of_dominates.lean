-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_IsHole_of_dominates
-- name    : DeciSigma1.Readers.StructuralReader.IsHole.of_dominates
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:43.262892+00:00
-- url     : https://prove2.me/theorems/16786c34-b90e-4a86-9d10-5fb31ae8d054
-- title:
--   Is Hole: of dominates
-- statement:
--   A tuple that dominates a hole is a hole with the same endpoints.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L594-L602
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L594-L602

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

theorem DeciSigma1.Readers.StructuralReader.IsHole.of_dominates [DecidableEq α] [DecidableEq S] {U W : Fin k → List α}
    (hW : M.IsHole W) (hU : Dominates M.toTable U W) :
    M.IsHole U ∧ ∀ i, M.endState U i = M.endState W i := by sorry
