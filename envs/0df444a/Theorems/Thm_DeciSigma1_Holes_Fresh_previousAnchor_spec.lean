-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_previousAnchor_spec
-- name    : DeciSigma1.Holes.Fresh.previousAnchor_spec
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:46:09.544552+00:00
-- url     : https://prove2.me/theorems/a26130da-bf31-4dce-9c40-796e958c06e9
-- title:
--   Fresh: previous Anchor spec
-- statement:
--   The Fresh construction uses the previous Anchor spec property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L153-L160
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Parsing.lean#L153-L160

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Hierarchy
public import Mathlib.Order.Nat
public import Mathlib.Algebra.GroupWithZero.Nat
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open Finset
variable {A : Finset ℕ}

theorem DeciSigma1.Holes.Fresh.previousAnchor_spec {p : ℕ} (h : ∃ q ∈ A, q < p) :
    previousAnchor A p ∈ A ∧ previousAnchor A p < p := by sorry
