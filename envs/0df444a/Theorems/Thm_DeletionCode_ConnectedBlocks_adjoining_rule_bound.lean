-- Prove2me | Theorems.Thm_DeletionCode_ConnectedBlocks_adjoining_rule_bound
-- name    : DeletionCode.ConnectedBlocks.adjoining_rule_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:19:42.272017+00:00
-- url     : https://prove2.me/theorems/bab81f91-c612-4906-8298-7e92f6577c57
-- title:
--   Connected Blocks: adjoining rule bound
-- statement:
--   The first assertion of the manuscript's connected-block lemma.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConnectedBlocks.lean#L94-L99
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConnectedBlocks.lean#L94-L99

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_ConnectedBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.ConnectedBlocks
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph

theorem DeletionCode.ConnectedBlocks.adjoining_rule_bound {t k : ℕ} (ht : 1 ≤ t)
    (U : RuleSet k) (w : Gram (windowLength k) → ℤ)
    (hw : CatalogueRule t k w) (hadj : ∃ u ∈ U, RuleAdjacent w u) :
    componentCount (insert w U) ≤ componentCount U + (2 * t - 1) := by sorry
