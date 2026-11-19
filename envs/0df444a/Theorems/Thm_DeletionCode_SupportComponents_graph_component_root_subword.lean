-- Prove2me | Theorems.Thm_DeletionCode_SupportComponents_graph_component_root_subword
-- name    : DeletionCode.SupportComponents.graph_component_root_subword
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-19T04:59:40.675968+00:00
-- url     : https://prove2.me/theorems/bfe64d5f-cc26-4419-8a24-e5d967cb5d5a
-- title:
--   Support Components: graph component root subword
-- statement:
--   Every vertex in the actual support graph reaches a root whose full negative
--   word occurs contiguously in x. No extra isolated ambient vertices are asserted
--   to have roots.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportComponents.lean#L244-L258
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportComponents.lean#L244-L258

import Definitions.Def_DeletionCode_RootSelection
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Card
import Definitions.Def_DeletionCode_SupportComponents
set_option autoImplicit true
open DeletionCode DeletionCode.SupportComponents
open Windows RootSelection

theorem DeletionCode.SupportComponents.graph_component_root_subword {B : Type*} (F : Family B)
    (x : Letters) (n k L : ℕ) (hx : KUnique x n k) (hk : k < L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    (hgen : F.Generating x n L) (v : SupportedVertex F L) :
    ∃ r a, GraphConnected F L v.val (representative F L r) ∧
      a + (L + F.extra r false) ≤ n ∧
      Agree x a (F.path r false) 0 (L + F.extra r false) := by sorry
