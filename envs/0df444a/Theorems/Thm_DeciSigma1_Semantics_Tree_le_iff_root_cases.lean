-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_le_iff_root_cases
-- name    : DeciSigma1.Semantics.Tree.le_iff_root_cases
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:39:16.935907+00:00
-- url     : https://prove2.me/theorems/2cfd11a3-ac88-45c7-b0fc-d0513c6c41b5
-- title:
--   Tree: le iff root cases
-- statement:
--   The Tree construction uses the le iff root cases property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L404-L419
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Tree.lean#L404-L419

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

theorem DeciSigma1.Semantics.Tree.le_iff_root_cases (t u : Tree n) :
    t ≤ u ↔ t = bot ∨ u = top ∨
      ∃ a b, t = node a ∧ u = node b ∧ ∀ i, a i ≤ b i := by sorry
