-- Prove2me | Theorems.Thm_DeletionCode_ConnectedBlocks_adjoining_rule_component_sum
-- name    : DeletionCode.ConnectedBlocks.adjoining_rule_component_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:19:31.44762+00:00
-- url     : https://prove2.me/theorems/2b1798a9-9346-46d4-99c1-8a883b977bbb
-- title:
--   Connected Blocks: adjoining rule component sum
-- statement:
--   A rule meeting the old support union saves one of its possible 2t components.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConnectedBlocks.lean#L73-L91
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConnectedBlocks.lean#L73-L91

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_ConnectedBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.ConnectedBlocks
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph

theorem DeletionCode.ConnectedBlocks.adjoining_rule_component_sum {t k : ℕ}
    (U : RuleSet k) (w : Gram (windowLength k) → ℤ)
    (hw : CatalogueRule t k w) (hadj : ∃ u ∈ U, RuleAdjacent w u) :
    componentCount (insert w U) + 1 ≤ componentCount U + 2 * t := by sorry
