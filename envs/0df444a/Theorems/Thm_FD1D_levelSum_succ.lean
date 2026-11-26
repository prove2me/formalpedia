-- Prove2me | Theorems.Thm_FD1D_levelSum_succ
-- name    : FD1D.levelSum_succ
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:49:08.196072+00:00
-- url     : https://prove2.me/theorems/c9451eb7-6c00-5eb7-aed8-e8b3edec7095
-- title:
--   FD1 D: level Sum succ
-- statement:
--   The FD1 D construction uses the level Sum succ property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L333-L337
-- source:
--   https://github.com/ykanoria/FD1d-Lean/blob/26a5b4e2fd83fa86053239e09e92af370c62f18c/FD1D/Tree.lean#L333-L337

import Definitions.Def_FD1D_Basic
import Definitions.Def_FD1D_Tree
set_option autoImplicit true
open FD1D
noncomputable section

theorem FD1D.levelSum_succ {A : Type*} [AddCommMonoid A]
    (f : ∀ d, DyadicNode d → A) (d : ℕ) :
    levelSum f (d + 1) =
      ∑ v, (f (d + 1) (leftChild v) + f (d + 1) (rightChild v)) := by sorry
