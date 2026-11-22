-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_eligible_congr
-- name    : DeciSigma1.Readers.StructuralReader.eligible_congr
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:32.041661+00:00
-- url     : https://prove2.me/theorems/b264c723-d0bd-42f8-9c59-2696d8789308
-- title:
--   Structural Reader: eligible congr
-- statement:
--   Eligibility of a coordinate depends only on its word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L490-L492
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L490-L492

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

theorem DeciSigma1.Readers.StructuralReader.eligible_congr {U W : Fin k → List α} {i : Fin k} (h : U i = W i) :
    M.Eligible U i ↔ M.Eligible W i := by sorry
