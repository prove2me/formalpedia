-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_dual_fn
-- name    : DeciSigma1.Semantics.dual_fn
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:14.72225+00:00
-- url     : https://prove2.me/theorems/102a3ec6-2899-46a2-870f-6232f0bf3e3e
-- title:
--   Semantics: dual fn
-- statement:
--   The Semantics construction uses the dual fn property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L139-L140
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L139-L140

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.dual_fn (t : Tree n) (π : List (Fin n)) :
    (Tree.dual t).fn π = (t.fn π).map (Sym.flip true) := by sorry
