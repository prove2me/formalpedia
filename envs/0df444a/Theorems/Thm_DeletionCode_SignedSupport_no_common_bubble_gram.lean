-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_no_common_bubble_gram
-- name    : DeletionCode.SignedSupport.no_common_bubble_gram
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T05:09:57.060004+00:00
-- url     : https://prove2.me/theorems/289c3cfb-54ae-4cc1-b2fe-a47ffaeb011f
-- title:
--   Signed Support: no common bubble gram
-- statement:
--   A shared edge would force both paths to consist of the same single edge,
--   contradicting their unequal lengths.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L92-L116
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L92-L116

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.no_common_bubble_gram {B : Type*} (F : Family B) (L : ℕ)
    (H : BubbleGeometry F L) (b : B) (g : Gram L)
    (hn : g ∈ windowSet (F.path b false) L (F.extra b false))
    (hp : g ∈ windowSet (F.path b true) L (F.extra b true)) : False := by sorry
