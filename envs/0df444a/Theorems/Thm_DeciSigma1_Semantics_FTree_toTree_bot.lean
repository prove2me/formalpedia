-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_FTree_toTree_bot
-- name    : DeciSigma1.Semantics.FTree.toTree_bot
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:31.508348+00:00
-- url     : https://prove2.me/theorems/1f01e465-3cd5-4435-b242-48178d7a2544
-- title:
--   FTree: to Tree bot
-- statement:
--   The FTree construction uses the to Tree bot property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L442-L442
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L442-L442

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
open DeciSigma1.Semantics.FTree
variable {n : ℕ}

theorem DeciSigma1.Semantics.FTree.toTree_bot : toTree (bot : FTree n) = Tree.bot := by sorry

attribute [defeq] DeciSigma1.Semantics.FTree.toTree_bot
