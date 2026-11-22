-- Prove2me | Theorems.Thm_DeciSigma1_Semantics_Tree_not_hasLabel_of_label
-- name    : DeciSigma1.Semantics.Tree.not_hasLabel_of_label
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-22T12:59:51.28287+00:00
-- url     : https://prove2.me/theorems/9e7b5cdb-d7b0-4bcb-b4a0-975a6e590e43
-- title:
--   Tree: not has Label of label
-- statement:
--   If `ν` is labeled `a`, no prefix of `ν` carries a leaf label `s` other than `a`.
--
--   Source: https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L295-L301
-- source:
--   https://github.com/LeanPool/lean-pool/blob/e110decb9d02249d99fa85a144e6a659dea91440/LeanPool/DeciSigma1/Semantics/Order.lean#L295-L301

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

theorem DeciSigma1.Semantics.Tree.not_hasLabel_of_label {t : Tree n} {ν : List (Fin n)} {a s : Sym}
    (h : t.fn ν = some a) (hs : s ≠ Sym.f) (ha : a ≠ s) : ¬ HasLabel t ν s := by sorry
