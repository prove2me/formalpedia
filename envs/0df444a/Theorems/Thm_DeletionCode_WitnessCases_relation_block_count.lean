-- Prove2me | Theorems.Thm_DeletionCode_WitnessCases_relation_block_count
-- name    : DeletionCode.WitnessCases.relation_block_count
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:25:26.861175+00:00
-- url     : https://prove2.me/theorems/876ad93a-3e97-4acd-93cb-e24f13a1caef
-- title:
--   Witness Cases: relation block count
-- statement:
--   Independence forces every selected block to meet w; support containment
--   then assigns distinct selected blocks to distinct actual components of w.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCases.lean#L37-L47
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCases.lean#L37-L47

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_FiniteRelationBlocks
import Definitions.Def_DeletionCode_SupportBlockCount
import Definitions.Def_DeletionCode_CatalogueAlgebra
import Definitions.Def_DeletionCode_LargeBlockSelection
import Definitions.Def_DeletionCode_WitnessCases
set_option autoImplicit true
open DeletionCode DeletionCode.WitnessCases
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks
open BlockPartition FiniteGenerating FiniteRelationBlocks CatalogueAlgebra
open scoped BigOperators

theorem DeletionCode.WitnessCases.relation_block_count {t k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (hind : Independent G)
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    (selectedBlocks G I).card ≤ 2 * t := by sorry
