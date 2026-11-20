-- Prove2me | Theorems.Thm_DeletionCode_ComponentBounds_unionComponentMap_surjective
-- name    : DeletionCode.ComponentBounds.unionComponentMap_surjective
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:12:36.601174+00:00
-- url     : https://prove2.me/theorems/9d36b405-3458-4a5e-84ab-75344eac905a
-- title:
--   Component Bounds: union Component Map surjective
-- statement:
--   The Component Bounds construction uses the union Component Map surjective property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ComponentBounds.lean#L67-L78
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ComponentBounds.lean#L67-L78

import Definitions.Def_DeletionCode_RuleSetGraph
import Mathlib.Data.Fintype.Sum
import Definitions.Def_DeletionCode_ComponentBounds
set_option autoImplicit true
open DeletionCode DeletionCode.ComponentBounds
open SignedSupport SupportComponents RuleSetGraph

theorem DeletionCode.ComponentBounds.unionComponentMap_surjective {L : ℕ} (Q S : Finset (Gram L → ℤ)) :
    Function.Surjective (unionComponentMap Q S) := by sorry
