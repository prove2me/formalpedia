-- Prove2me | Theorems.Thm_DeletionCode_SupportComponents_bubble_vertices_connected
-- name    : DeletionCode.SupportComponents.bubble_vertices_connected
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:59:29.956002+00:00
-- url     : https://prove2.me/theorems/0104a111-388f-44d2-82fd-f7e4522a9e20
-- title:
--   Support Components: bubble vertices connected
-- statement:
--   All vertices of one bubble are internally connected by its actual path edges.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportComponents.lean#L79-L87
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportComponents.lean#L79-L87

import Definitions.Def_DeletionCode_RootSelection
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Card
import Definitions.Def_DeletionCode_SupportComponents
set_option autoImplicit true
open DeletionCode DeletionCode.SupportComponents
open Windows RootSelection

theorem DeletionCode.SupportComponents.bubble_vertices_connected {B : Type*} (F : Family B) (L : ℕ)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (b : B) (u v : Vertex L) (hu : HasVertex F L b u) (hv : HasVertex F L b v) :
    GraphConnected F L u v := by sorry
