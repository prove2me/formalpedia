-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_signed_generating_implies_generating
-- name    : DeletionCode.SignedSupport.signed_generating_implies_generating
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:12:25.424365+00:00
-- url     : https://prove2.me/theorems/c8a398e8-c8d6-4837-a0c9-c514bb103772
-- title:
--   Signed Support: signed generating implies generating
-- statement:
--   The concrete word-level generating premise is derived from signed spectra
--   and catalogue geometry, not assumed as another provenance hypothesis.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L282-L303
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L282-L303

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.signed_generating_implies_generating {B : Type*} [Fintype B]
    (F : Family B) (x : Letters) (n L : ℕ)
    (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i))
    (hgen : SignedGenerating F x n L) : F.Generating x n L := by sorry
