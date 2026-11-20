-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_supported_iff_signed_incident
-- name    : DeletionCode.SignedSupport.supported_iff_signed_incident
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:18:36.25419+00:00
-- url     : https://prove2.me/theorems/0f4a0aca-141a-432b-9190-aed03f2ba5cf
-- title:
--   Signed Support: supported iff signed incident
-- statement:
--   The path vertex union is exactly the incident-vertex set of the signed
--   support union. In particular the restriction excludes every ambient outsider.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L361-L384
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L361-L384

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.supported_iff_signed_incident {B : Type*} [Fintype B]
    (F : Family B) (L : ℕ) (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i))
    (v : SupportComponents.Vertex L) :
    (∃ b, SupportComponents.HasVertex F L b v) ↔
      ∃ w, signedSupportEdge F L v w ∨ signedSupportEdge F L w v := by sorry
