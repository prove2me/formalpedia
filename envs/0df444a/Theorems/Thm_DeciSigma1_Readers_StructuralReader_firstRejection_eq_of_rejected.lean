-- Prove2me | Theorems.Thm_DeciSigma1_Readers_StructuralReader_firstRejection_eq_of_rejected
-- name    : DeciSigma1.Readers.StructuralReader.firstRejection_eq_of_rejected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:57:36.269186+00:00
-- url     : https://prove2.me/theorems/3803748b-8d98-409c-bc63-d02ea40bddf3
-- title:
--   Structural Reader: first Rejection eq of rejected
-- statement:
--   The first rejected cut is the cut that is rejected and preceded only by cuts that are not.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L548-L558
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Readers/Basic.lean#L548-L558

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

theorem DeciSigma1.Readers.StructuralReader.firstRejection_eq_of_rejected
    {M : StructuralReader α S k} {W : Fin k → List α}
    {i : Fin k} (h : M.Eligible W i) {a : ℕ}
    (hr : M.rejected (M.runPrefix W i a) = true)
        (hb : ∀ a' < a, M.rejected (M.runPrefix W i a') = false) :
    M.firstRejection W i = a := by sorry
