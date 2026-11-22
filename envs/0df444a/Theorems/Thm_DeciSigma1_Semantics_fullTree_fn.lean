-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_fullTree_fn
-- name    : DeciSigma1.Semantics.fullTree_fn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T13:26:06.233282+00:00
-- url     : https://prove2.me/theorems/7c309b30-5f2d-469f-8142-8254803bdd9d
-- title:
--   Semantics: full Tree fn
-- statement:
--   The Semantics construction uses the full Tree fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Median.lean#L233-L233
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Median.lean#L233-L233

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

theorem DeciSigma1.Semantics.fullTree_fn (w : List (Fin n)) : (fullTree : Tree n).fn w = some .f := by sorry

attribute [defeq] DeciSigma1.Semantics.fullTree_fn
