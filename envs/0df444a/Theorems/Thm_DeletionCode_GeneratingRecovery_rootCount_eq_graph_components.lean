-- Prove2me | Theorems.Thm_DeletionCode_GeneratingRecovery_rootCount_eq_graph_components
-- name    : DeletionCode.GeneratingRecovery.rootCount_eq_graph_components
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T05:15:47.614669+00:00
-- url     : https://prove2.me/theorems/e8520f95-45c7-4cb8-84cc-e0454a20e741
-- title:
--   Generating Recovery: root Count eq graph components
-- statement:
--   The Generating Recovery construction uses the root Count eq graph components property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingRecovery.lean#L61-L67
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingRecovery.lean#L61-L67

import Definitions.Def_DeletionCode_GeneratingModel
import Definitions.Def_DeletionCode_ConcreteRecovery
import Definitions.Def_DeletionCode_SupportComponents
import Definitions.Def_DeletionCode_GeneratingRecovery
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingRecovery
open Windows HeaderRecovery GeneratingModel ConcreteDecoder
variable {B : Type*} {k : ℕ}

theorem DeletionCode.GeneratingRecovery.rootCount_eq_graph_components [Fintype B]
    (E : EditedFamily B k) (x : Letters) (n : ℕ)
    (hx : KUnique x n k) (hg : E.family.Generating x n (windowLength k)) :
    ConcreteInitialization.rootCount (model E x n hx hg) =
      Fintype.card (SupportComponents.GraphComponents E.family (windowLength k)) := by sorry
