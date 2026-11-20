-- Prove2me | Theorems.Thm_DeletionCode_ConnectedBlocks_catalogue_singleton_component_count_le
-- name    : DeletionCode.ConnectedBlocks.catalogue_singleton_component_count_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:19:34.951981+00:00
-- url     : https://prove2.me/theorems/911826d7-e898-47f8-8a5c-7dac9b1ce0bf
-- title:
--   Connected Blocks: catalogue singleton component count le
-- statement:
--   A catalogue rule has at most 2t components of its actual signed support.
--   This follows from the proved support-graph equivalence and its 2t path bubbles.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConnectedBlocks.lean#L61-L70
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/ConnectedBlocks.lean#L61-L70

import Definitions.Def_DeletionCode_ComponentBounds
import Definitions.Def_DeletionCode_CatalogueBridge
import Definitions.Def_DeletionCode_FiniteConnectedGrowth
import Definitions.Def_DeletionCode_ConnectedBlocks
set_option autoImplicit true
open DeletionCode DeletionCode.ConnectedBlocks
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph

theorem DeletionCode.ConnectedBlocks.catalogue_singleton_component_count_le {t k : ℕ}
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w) :
    componentCount {w} ≤ 2 * t := by sorry
