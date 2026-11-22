-- Prove2me | Theorems.Thm_DeciSigma1_Holes_Fresh_prefix_drop_of_occ
-- name    : DeciSigma1.Holes.Fresh.prefix_drop_of_occ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:50:28.918855+00:00
-- url     : https://prove2.me/theorems/7705e060-05ac-4102-99d5-4025d902d540
-- title:
--   Fresh: prefix drop of occ
-- statement:
--   The Fresh construction uses the prefix drop of occ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L64-L72
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Holes/Fresh/Deletion.lean#L64-L72

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
omit [DecidableEq α]

theorem DeciSigma1.Holes.Fresh.prefix_drop_of_occ {x u v : List α} {i j : ℕ} (hu : u <+: x.drop i)
    (hv : v <+: x.drop j) (hij : i ≤ j) (hlen : j + v.length ≤ i + u.length) :
    v <+: u.drop (j - i) := by sorry
