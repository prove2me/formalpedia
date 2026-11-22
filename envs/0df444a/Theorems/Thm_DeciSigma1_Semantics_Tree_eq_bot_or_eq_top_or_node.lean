-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_eq_bot_or_eq_top_or_node
-- name    : DeciSigma1.Semantics.Tree.eq_bot_or_eq_top_or_node
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:34:48.509807+00:00
-- url     : https://prove2.me/theorems/082535e0-b626-4d07-9832-b22694cb8a2d
-- title:
--   Tree: eq bot or eq top or node
-- statement:
--   The Tree construction uses the eq bot or eq top or node property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L279-L285
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L279-L285

module
public import Mathlib.Algebra.Order.Ring.Nat
public import Mathlib.Data.List.Induction
public import Mathlib.Tactic.Attr.Core
public import Mathlib.Order.Lattice
public import Definitions.Def_LeanPool_DeciSigma1_Semantics_Tree
set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Semantics
open DeciSigma1.Semantics.Tree
variable {n : ℕ}

theorem DeciSigma1.Semantics.Tree.eq_bot_or_eq_top_or_node (t : Tree n) :
    t = bot ∨ t = top ∨ ∃ a, t = node a := by sorry
