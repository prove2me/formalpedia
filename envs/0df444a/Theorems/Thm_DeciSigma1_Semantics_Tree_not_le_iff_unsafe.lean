-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_not_le_iff_unsafe
-- name    : DeciSigma1.Semantics.Tree.not_le_iff_unsafe
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:48.177665+00:00
-- url     : https://prove2.me/theorems/27ab3172-4225-426b-8d81-29f33dcd37c1
-- title:
--   Tree: not le iff unsafe
-- statement:
--   `t ≤ u` fails exactly when some path leads `t` to a tree other than `⊥` and `u` to `⊥`, or
--   leads `t` to `⊤` and `u` to a tree other than `⊤`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L305-L330
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L305-L330

module
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
public import Mathlib.Tactic.Bound.Init
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Order
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
variable {n : ℕ}
open DeciSigma1.Semantics.Tree

theorem DeciSigma1.Semantics.Tree.not_le_iff_unsafe (t u : Tree n) :
    ¬ t ≤ u ↔ ∃ ν, (trace t ν ≠ Tree.bot ∧ trace u ν = Tree.bot) ∨
      (trace t ν = Tree.top ∧ trace u ν ≠ Tree.top) := by sorry
