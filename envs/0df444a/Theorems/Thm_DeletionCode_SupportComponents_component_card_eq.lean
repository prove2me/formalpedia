-- Prove2me | Theorems.Thm_DeletionCode_SupportComponents_component_card_eq
-- name    : DeletionCode.SupportComponents.component_card_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T04:59:43.306961+00:00
-- url     : https://prove2.me/theorems/e8d552a3-f1ca-4664-9514-99e34d7cd460
-- title:
--   Support Components: component card eq
-- statement:
--   Consequently any finite cardinality representations give the same component count.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportComponents.lean#L235-L239
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/SupportComponents.lean#L235-L239

import Definitions.Def_DeletionCode_RootSelection
import Mathlib.Logic.Equiv.Defs
import Mathlib.Data.Fintype.Card
import Definitions.Def_DeletionCode_SupportComponents
set_option autoImplicit true
open DeletionCode DeletionCode.SupportComponents
open Windows RootSelection

theorem DeletionCode.SupportComponents.component_card_eq {B : Type*} (F : Family B) (L : ℕ) (hL : 1 ≤ L)
    (hstart : ∀ b, vertex F L b false 0 = vertex F L b true 0)
    [Fintype (Components F L)] [Fintype (GraphComponents F L)] :
    Fintype.card (Components F L) = Fintype.card (GraphComponents F L) := by sorry
