-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_top_treeLe_iff
-- name    : DeciSigma1.Semantics.top_treeLe_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:10.151625+00:00
-- url     : https://prove2.me/theorems/5b0069c7-36bb-4585-a205-236429532b21
-- title:
--   Semantics: top tree Le iff
-- statement:
--   The Semantics construction uses the top tree Le iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L401-L402
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L401-L402

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

theorem DeciSigma1.Semantics.top_treeLe_iff (c : Fin n → Bool) (t : Tree n) : Le c top t ↔ t = top := by sorry
