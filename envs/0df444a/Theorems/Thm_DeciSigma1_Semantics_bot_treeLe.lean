-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_bot_treeLe
-- name    : DeciSigma1.Semantics.bot_treeLe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:35:59.573805+00:00
-- url     : https://prove2.me/theorems/29612481-fefd-4079-b54e-7240307e8e75
-- title:
--   Semantics: bot tree Le
-- statement:
--   The Semantics construction uses the bot tree Le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L395-L396
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L395-L396

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

theorem DeciSigma1.Semantics.bot_treeLe (c : Fin n → Bool) (t : Tree n) : Le c bot t := by sorry
