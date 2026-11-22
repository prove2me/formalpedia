-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_le_bot_iff
-- name    : DeciSigma1.Semantics.Tree.le_bot_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:33:13.309792+00:00
-- url     : https://prove2.me/theorems/1477c935-bf31-4734-b20b-80039fec836a
-- title:
--   Tree: le bot iff
-- statement:
--   The Tree construction uses the le bot iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L388-L389
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L388-L389

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

theorem DeciSigma1.Semantics.Tree.le_bot_iff (t : Tree n) : t ≤ bot ↔ t = bot := by sorry
