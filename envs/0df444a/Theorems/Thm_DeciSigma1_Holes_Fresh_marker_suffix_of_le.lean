-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_marker_suffix_of_le
-- name    : DeciSigma1.Holes.Fresh.marker_suffix_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:32.940012+00:00
-- url     : https://prove2.me/theorems/f9f63922-4504-4b71-985a-787bc1176090
-- title:
--   Fresh: marker suffix of le
-- statement:
--   The Fresh construction uses the marker suffix of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L78-L83
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L78-L83

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

theorem DeciSigma1.Holes.Fresh.marker_suffix_of_le {W : Fin k → List α} {r t : ℕ} (hrt : r ≤ t)
    {m : Fin k} (hm : m ∈ active W t) : marker W r m <:+ marker W t m := by sorry
