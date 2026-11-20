-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_signed_support_edge_iff
-- name    : DeletionCode.SignedSupport.signed_support_edge_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:10:29.297452+00:00
-- url     : https://prove2.me/theorems/5e9cf6cf-6f8a-4572-85c5-f540b08e1020
-- title:
--   Signed Support: signed support edge iff
-- statement:
--   The actual signed-support graph has precisely the consecutive-window edges
--   used by SupportComponents. No cancellation is assumed in this identification.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L334-L357
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L334-L357

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.signed_support_edge_iff {B : Type*} [Fintype B]
    (F : Family B) (L : ℕ) (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i))
    (u v : SupportComponents.Vertex L) :
    signedSupportEdge F L u v ↔ SupportComponents.Edge F L u v := by sorry
