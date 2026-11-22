-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_sitePositions_insert
-- name    : DeciSigma1.Holes.Fresh.sitePositions_insert
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:03:46.951806+00:00
-- url     : https://prove2.me/theorems/26beb221-d12c-40b4-a20a-91ab3216fdce
-- title:
--   Fresh: site Positions insert
-- statement:
--   The Fresh construction uses the site Positions insert property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L261-L263
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L261-L263

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
variable {δ : ℕ} {cs : Finset ℕ}

theorem DeciSigma1.Holes.Fresh.sitePositions_insert (c : ℕ) (cs : Finset ℕ) :
    sitePositions δ (insert c cs) = sitePositions δ cs ∪ Finset.Ico c (c + δ) := by sorry
