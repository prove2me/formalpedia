-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_length_deleteSite
-- name    : DeciSigma1.Holes.Fresh.length_deleteSite
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:54:49.151227+00:00
-- url     : https://prove2.me/theorems/05c0c4ca-dc85-48e8-8d83-8000847908a8
-- title:
--   Fresh: length delete Site
-- statement:
--   The Fresh construction uses the length delete Site property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L159-L161
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L159-L161

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
variable {W : Fin k → List α}
omit [DecidableEq α]

theorem DeciSigma1.Holes.Fresh.length_deleteSite {x : List α} {c δ : ℕ} (h : c + δ ≤ x.length) :
    (x.take c ++ x.drop (c + δ)).length = x.length - δ := by sorry
