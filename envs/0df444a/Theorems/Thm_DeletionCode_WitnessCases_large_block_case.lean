-- Prove2me | Theorems.Thm_DeletionCode_WitnessCases_large_block_case
-- name    : DeletionCode.WitnessCases.large_block_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:25:26.062818+00:00
-- url     : https://prove2.me/theorems/500f4132-ff45-4a84-b1a6-92f4e5b2c398
-- title:
--   Witness Cases: large block case
-- statement:
--   A cutoff failure after an independent append selects its actual new block,
--   with both the strict lower cutoff and the full manuscript upper bounds.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCases.lean#L112-L138
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCases.lean#L112-L138

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

theorem DeletionCode.WitnessCases.large_block_case {t k : ℕ} (ht : 2 ≤ t)
    (v : Gram (windowLength k) → ℤ) (K : Set (Gram (windowLength k) → ℤ))
    (G : RuleSet k) (w : Gram (windowLength k) → ℤ)
    (hgen : GeneratingAt v (insert w G)) (hw : CatalogueRule t k w)
    (hcat : ∀ u ∈ G, CatalogueRule t k u)
    (hK : ∀ u ∈ insert w G, u ∈ K)
    (hsize : ∀ B ∈ blocks G, B.card ≤ windowLength k)
    (hbad : ¬ ∀ B ∈ blocks (insert w G), B.card ≤ windowLength k) :
    Witness t k v K (blockOf (insert w G) w) := by sorry
