-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_fullTree_eq_node
-- name    : DeciSigma1.Semantics.fullTree_eq_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:31:07.2522+00:00
-- url     : https://prove2.me/theorems/b2eecc2a-ba28-43db-9d73-56a98c9c5142
-- title:
--   Semantics: full Tree eq node
-- statement:
--   The Semantics construction uses the full Tree eq node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Median.lean#L235-L236
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Median.lean#L235-L236

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
public import Mathlib.Tactic.Bound.Init
public import Mathlib.Data.List.Induction
public import Mathlib.Order.MinMax
public import Mathlib.Data.Finset.Attr
public import Mathlib.Tactic.SetLike
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Median
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.fullTree_eq_node : (fullTree : Tree n) = Tree.node (fun _ => fullTree) := by sorry
