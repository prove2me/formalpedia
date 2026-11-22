-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_treeLe_bot_iff
-- name    : DeciSigma1.Semantics.treeLe_bot_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:05.782802+00:00
-- url     : https://prove2.me/theorems/02735f3e-db40-4b9f-96b3-42b24ba84cc8
-- title:
--   Semantics: tree Le bot iff
-- statement:
--   The Semantics construction uses the tree Le bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L399-L400
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L399-L400

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

theorem DeciSigma1.Semantics.treeLe_bot_iff (c : Fin n → Bool) (t : Tree n) : Le c t bot ↔ t = bot := by sorry
