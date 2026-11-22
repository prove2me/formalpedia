-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_treeLe_iff_normalize
-- name    : DeciSigma1.Semantics.treeLe_iff_normalize
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:12.708785+00:00
-- url     : https://prove2.me/theorems/0e3331ae-9f5c-48d9-8463-6df1c79796e8
-- title:
--   Semantics: tree Le iff normalize
-- statement:
--   The order with variance `c` is the covariant order on normalizations.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L369-L378
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L369-L378

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.treeLe_iff_normalize (c : Fin n → Bool) (t u : Tree n) :
    Le c t u ↔ Tree.normalize c false t ≤ Tree.normalize c false u := by sorry
