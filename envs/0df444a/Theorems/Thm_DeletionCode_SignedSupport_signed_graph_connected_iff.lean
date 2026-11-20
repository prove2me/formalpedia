-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_signed_graph_connected_iff
-- name    : DeletionCode.SignedSupport.signed_graph_connected_iff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:11:55.372807+00:00
-- url     : https://prove2.me/theorems/3c4fd565-1486-4d48-bf09-e9e3132d8048
-- title:
--   Signed Support: signed graph connected iff
-- statement:
--   The Signed Support construction uses the signed graph connected iff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L390-L399
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L390-L399

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.signed_graph_connected_iff {B : Type*} [Fintype B]
    (F : Family B) (L : ℕ) (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i))
    (u v : SupportComponents.Vertex L) :
    SignedGraphConnected F L u v ↔ SupportComponents.GraphConnected F L u v := by sorry
