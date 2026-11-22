-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_take_deleteSite_of_ge
-- name    : DeciSigma1.Holes.Fresh.take_deleteSite_of_ge
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:45.097885+00:00
-- url     : https://prove2.me/theorems/02a17891-a482-4040-833e-5eeee3f08ed8
-- title:
--   Fresh: take delete Site of ge
-- statement:
--   The Fresh construction uses the take delete Site of ge property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L148-L151
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L148-L151

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

theorem DeciSigma1.Holes.Fresh.take_deleteSite_of_ge {x : List α} {c δ e : ℕ} (hc : c ≤ x.length) (he : c ≤ e) :
    (x.take c ++ x.drop (c + δ)).take e = x.take c ++ (x.drop (c + δ)).take (e - c) := by sorry
