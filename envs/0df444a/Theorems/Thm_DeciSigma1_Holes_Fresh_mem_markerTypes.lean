-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_mem_markerTypes
-- name    : DeciSigma1.Holes.Fresh.mem_markerTypes
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:43:58.071051+00:00
-- url     : https://prove2.me/theorems/40d884ad-b6c4-41c0-b412-b7a190965130
-- title:
--   Fresh: mem marker Types
-- statement:
--   The Fresh construction uses the mem marker Types property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L387-L389
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L387-L389

module
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Parsing
public import Definitions.Def_LeanPool_DeciSigma1_Words_Deletion
public import Mathlib.Data.Finset.Max
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_Deletion
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Fresh
open DeciSigma1.Readers DeciSigma1.Words
open Finset
variable {α : Type} [DecidableEq α] {k : ℕ}
variable {S : Type} [DecidableEq S]

theorem DeciSigma1.Holes.Fresh.mem_markerTypes {W : Fin k → List α} {r : ℕ} {u : List α} {c : ℕ} {τ : List α} :
    τ ∈ markerTypes W r u c ↔ ∃ m ∈ active W r, marker W r m <:+ u.take c ∧ marker W r m = τ := by sorry
