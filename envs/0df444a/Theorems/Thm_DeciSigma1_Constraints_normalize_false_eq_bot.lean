-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_normalize_false_eq_bot
-- name    : DeciSigma1.Constraints.normalize_false_eq_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:16.673748+00:00
-- url     : https://prove2.me/theorems/085013cf-d694-4a2f-9614-a7594fb70f5f
-- title:
--   Constraints: normalize false eq bot
-- statement:
--   The Constraints construction uses the normalize false eq bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L125-L129
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L125-L129

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

theorem DeciSigma1.Constraints.normalize_false_eq_bot (c : Fin n → Bool) (t : Semantics.Tree n) :
    Tree.normalize c false t = Tree.bot ↔ t = Tree.bot := by sorry
