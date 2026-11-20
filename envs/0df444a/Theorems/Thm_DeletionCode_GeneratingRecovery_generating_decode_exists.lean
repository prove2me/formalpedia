-- Prove2me | Theorems.Thm_DeletionCode_GeneratingRecovery_generating_decode_exists
-- name    : DeletionCode.GeneratingRecovery.generating_decode_exists
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:15:52.840215+00:00
-- url     : https://prove2.me/theorems/f459cfaa-e72f-4558-8cdc-924b41f5d5d1
-- title:
--   Generating Recovery: generating decode exists
-- statement:
--   Every generating edited family has a bounded successful concrete decoding record.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingRecovery.lean#L70-L81
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingRecovery.lean#L70-L81

import Definitions.Def_DeletionCode_GeneratingModel
import Definitions.Def_DeletionCode_ConcreteRecovery
import Definitions.Def_DeletionCode_SupportComponents
import Definitions.Def_DeletionCode_GeneratingRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingRecovery
open Windows HeaderRecovery GeneratingModel ConcreteDecoder
variable {B : Type*} {k : ℕ}

theorem DeletionCode.GeneratingRecovery.generating_decode_exists [Fintype B] [DecidableEq B]
    (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    ∃ roots instructions,
      roots.length = Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) ∧
      instructions.length ≤ 4 * Fintype.card B ∧
      decode x n k E.header roots instructions =
        some (fun b i => negativePath k (E.header b) (E.long b) i.val) := by sorry
