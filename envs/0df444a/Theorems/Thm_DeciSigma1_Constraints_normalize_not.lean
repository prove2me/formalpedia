-- Prove2me | Theorems.Thm_DeciSigma1_Constraints_normalize_not
-- name    : DeciSigma1.Constraints.normalize_not
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:37:13.566093+00:00
-- url     : https://prove2.me/theorems/86c61540-dbf4-4c9b-a900-1ab0517f74a5
-- title:
--   Constraints: normalize not
-- statement:
--   The Constraints construction uses the normalize not property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L122-L123
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Constraints/Signed.lean#L122-L123

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

theorem DeciSigma1.Constraints.normalize_not (c : Fin n → Bool) (p : Bool) (t : Semantics.Tree n) :
    Tree.normalize c (!p) t = Tree.dual (Tree.normalize c p t) := by sorry
