-- Prove2me | Theorems.Thm_DeletionCode_WitnessCases_relation_case
-- name    : DeletionCode.WitnessCases.relation_case
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:25:28.753322+00:00
-- url     : https://prove2.me/theorems/b9bcef13-9b4f-439e-993d-26901da27eae
-- title:
--   Witness Cases: relation case
-- statement:
--   Retaining whole blocks in the relation case gives the full bounded
--   witness, including the stronger component bound for every resulting size.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCases.lean#L71-L92
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCases.lean#L71-L92

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

theorem DeletionCode.WitnessCases.relation_case {t k : ℕ} (ht : 2 ≤ t)
    (v : Gram (windowLength k) → ℤ) (K : Set (Gram (windowLength k) → ℤ))
    (G I : RuleSet k) (hIG : I ⊆ G) (hI : 2 ≤ I.card)
    (hgen : GeneratingAt v G) (hcat : ∀ u ∈ G, CatalogueRule t k u)
    (hK : ∀ u ∈ G, u ∈ K) (hsize : ∀ B ∈ blocks G, B.card ≤ windowLength k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ)) :
    Witness t k v K (RelationBlockSavings.blockHull G I) := by sorry
