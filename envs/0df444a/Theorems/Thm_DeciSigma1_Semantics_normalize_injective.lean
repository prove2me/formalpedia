-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_normalize_injective
-- name    : DeciSigma1.Semantics.normalize_injective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:35.422116+00:00
-- url     : https://prove2.me/theorems/d08debed-b592-415f-a967-37dda6ab8f85
-- title:
--   Semantics: normalize injective
-- statement:
--   The Semantics construction uses the normalize injective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L110-L112
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L110-L112

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.normalize_injective (c : Fin n → Bool) (p : Bool) :
    Function.Injective (Tree.normalize c p) := by sorry
