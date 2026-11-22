-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_dual_eq_bot
-- name    : DeciSigma1.Constraints.dual_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:36:55.914929+00:00
-- url     : https://prove2.me/theorems/62199576-3e09-46c7-8905-1fcde0e6ca69
-- title:
--   Constraints: dual eq bot
-- statement:
--   The Constraints construction uses the dual eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L79-L82
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L79-L82

module
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Basic
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Constraints_Signed
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Constraints
open DeciSigma1.Constraints.Covariant DeciSigma1.Semantics
variable {n : ℕ} {V : Type*}

theorem DeciSigma1.Constraints.dual_eq_bot (t : Semantics.Tree n) : Tree.dual t = Tree.bot ↔ t = Tree.top := by sorry
