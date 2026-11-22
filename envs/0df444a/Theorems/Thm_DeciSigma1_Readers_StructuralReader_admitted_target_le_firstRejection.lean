-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_admitted_target_le_firstRejection
-- name    : DeciSigma1.Readers.StructuralReader.admitted_target_le_firstRejection
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:36.824582+00:00
-- url     : https://prove2.me/theorems/e0728710-8ea3-42ed-8ed2-2f25452448d8
-- title:
--   Structural Reader: admitted target le first Rejection
-- statement:
--   On an eligible target coordinate, an admitted target state lies at or before the first
--   rejected cut.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L562-L572
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L562-L572

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

theorem DeciSigma1.Readers.StructuralReader.admitted_target_le_firstRejection {W : Fin k → List α} {j : Fin k} {b : ℕ} {p : S}
    (h : M.Eligible W j) (hb : b ≤ (W j).length) (hadm : M.admitted p (M.runPrefix W j b) = true) :
    b ≤ M.firstRejection W j := by sorry
