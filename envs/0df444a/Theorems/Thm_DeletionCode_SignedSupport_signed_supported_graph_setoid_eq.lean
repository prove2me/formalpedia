-- Prove2me | Theorems.Thm_DeletionCode_SignedSupport_signed_supported_graph_setoid_eq
-- name    : DeletionCode.SignedSupport.signed_supported_graph_setoid_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:03:53.232754+00:00
-- url     : https://prove2.me/theorems/f40afb77-20ba-44d3-a7c8-5e5f1dfb4fdc
-- title:
--   Signed Support: signed supported graph setoid eq
-- statement:
--   Hence the existing supported-graph component quotient counts exactly the
--   components of the signed support union, with the same incident vertex set.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L410-L416
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SignedSupport.lean#L410-L416

import Definitions.Def_DeletionCode_SupportComponents
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Pi
import Definitions.Def_DeletionCode_SignedSupport
set_option autoImplicit true
open DeletionCode DeletionCode.SignedSupport
open Windows RootSelection
open scoped BigOperators

theorem DeletionCode.SignedSupport.signed_supported_graph_setoid_eq {B : Type*} [Fintype B]
    (F : Family B) (L : ℕ) (H : BubbleGeometry F L)
    (hdis : ∀ i, VertexDisjointOn F L (ruleBubbles F i)) :
    signedSupportedGraphSetoid F L = SupportComponents.supportedGraphSetoid F L := by sorry
