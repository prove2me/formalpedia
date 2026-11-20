-- Prove2me | Theorems.Thm_DeletionCode_ConcreteFill_fillFromBase_extends
-- name    : DeletionCode.ConcreteFill.fillFromBase_extends
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:56:24.729104+00:00
-- url     : https://prove2.me/theorems/079c31fc-a844-4772-acc1-effcdbe43e3a
-- title:
--   Concrete Fill: fill From Base extends
-- statement:
--   Even arbitrary base-fill inputs cannot overwrite an already recorded bit.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteFill.lean#L97-L109
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConcreteFill.lean#L97-L109

import Definitions.Def_DeletionCode_PartialWords
import Definitions.Def_DeletionCode_SeedLookup
import Definitions.Def_DeletionCode_ConcreteFill
set_option autoImplicit true
open DeletionCode DeletionCode.ConcreteFill
open Windows PartialWords

theorem DeletionCode.ConcreteFill.fillFromBase_extends (x : Letters) (n k L : ℕ)
    (s t : Memory) (m start r : ℕ)
    (h : fillFromBase x n k L s m start r = some t) : Extends s t := by sorry
