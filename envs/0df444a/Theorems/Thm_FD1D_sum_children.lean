-- Prove2me | Theorems.Thm_FD1D_sum_children
-- name    : FD1D.sum_children
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:48:40.754275+00:00
-- url     : https://prove2.me/theorems/66f4f252-345d-5c40-b307-9521e7f4483d
-- title:
--   FD1 D: sum children
-- statement:
--   Every node at level `d+1` occurs exactly once as a left or right child.
--   This is the basic child-partition identity for finite sums.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L65-L78
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L65-L78

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.sum_children {M : Type*} [AddCommMonoid M] (d : ℕ)
    (f : DyadicNode (d + 1) → M) :
    ∑ w, f w = ∑ v, (f (leftChild v) + f (rightChild v)) := by sorry
