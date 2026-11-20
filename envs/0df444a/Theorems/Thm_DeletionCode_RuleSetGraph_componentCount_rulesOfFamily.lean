-- Prove2me | Theorems.Thm_DeletionCode_RuleSetGraph_componentCount_rulesOfFamily
-- name    : DeletionCode.RuleSetGraph.componentCount_rulesOfFamily
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:07:56.350245+00:00
-- url     : https://prove2.me/theorems/02b42345-4baa-4e57-ad84-5547bf6bc5d9
-- title:
--   Rule Set Graph: component Count rules Of Family
-- statement:
--   The c used by recovery is the intrinsic number of signed-support components.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleSetGraph.lean#L173-L182
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/RuleSetGraph.lean#L173-L182

import Definitions.Def_DeletionCode_RuleReconstruction
import Mathlib.SetTheory.Cardinal.Finite
import Definitions.Def_DeletionCode_RuleSetGraph
set_option autoImplicit true
open DeletionCode DeletionCode.RuleSetGraph
open Windows HeaderRecovery GeneratingModel RootSelection
open SignedSupport RuleReconstruction SupportComponents

theorem DeletionCode.RuleSetGraph.componentCount_rulesOfFamily {ν R k : ℕ} (E : EditedFamily (Fin ν) k)
    (group : Fin ν → Fin R) (hrank : ∀ b, E.rank b = (group b).val)
    (H : BubbleGeometry E.family (windowLength k))
    (hdis : ∀ i, VertexDisjointOn E.family (windowLength k) (ruleBubbles E.family i)) :
    componentCount (rulesOfFamily E group) =
      Fintype.card (GraphComponents E.family (windowLength k)) := by sorry
