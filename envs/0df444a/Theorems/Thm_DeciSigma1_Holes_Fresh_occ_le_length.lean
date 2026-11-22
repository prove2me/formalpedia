-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_occ_le_length
-- name    : DeciSigma1.Holes.Fresh.occ_le_length
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:49:28.878119+00:00
-- url     : https://prove2.me/theorems/11ffce38-c814-44de-a83e-d1e958a6b1f0
-- title:
--   Fresh: occ le length
-- statement:
--   A nonempty word occurring at position `i` fits into the word.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L111-L116
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Hierarchy.lean#L111-L116

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Readers_Basic
public import Mathlib.Order.Nat
public import Mathlib.Algebra.Group.Action.Defs
public import Mathlib.Order.Interval.Finset.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers
open Finset
variable {α : Type} {k : ℕ}
variable {x u v : List α}

theorem DeciSigma1.Holes.Fresh.occ_le_length {i : ℕ} (hu : u <+: x.drop i) (hne : u ≠ []) :
    i + u.length ≤ x.length := by sorry
