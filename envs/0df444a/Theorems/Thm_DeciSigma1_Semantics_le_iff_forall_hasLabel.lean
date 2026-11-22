-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_le_iff_forall_hasLabel
-- name    : DeciSigma1.Semantics.le_iff_forall_hasLabel
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:22.233927+00:00
-- url     : https://prove2.me/theorems/47658ad4-13fe-4c6a-abda-fc946cfe27fb
-- title:
--   Semantics: le iff forall has Label
-- statement:
--   `t ≤ u` in the covariant order exactly when along every path, `u` reaches `⊤` whenever `t`
--   does and `t` reaches `⊥` whenever `u` does.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L336-L355
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L336-L355

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}

theorem DeciSigma1.Semantics.le_iff_forall_hasLabel (t u : Tree n) :
    t ≤ u ↔ ∀ π, (t.HasLabel π .top → u.HasLabel π .top) ∧
      (u.HasLabel π .bot → t.HasLabel π .bot) := by sorry
