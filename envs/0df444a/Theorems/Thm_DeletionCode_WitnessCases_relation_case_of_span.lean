-- Prove2me | Theorems.Thm_DeletionCode_WitnessCases_relation_case_of_span
-- name    : DeletionCode.WitnessCases.relation_case_of_span
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:25:31.163889+00:00
-- url     : https://prove2.me/theorems/08eb80db-4817-44e7-b0ec-4f7d05909617
-- title:
--   Witness Cases: relation case of span
-- statement:
--   Novelty up to sign derives a relation with at least two active coefficients,
--   so no relation-support set is assumed in the in-span stopping case.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCases.lean#L96-L108
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCases.lean#L96-L108

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

theorem DeletionCode.WitnessCases.relation_case_of_span {t k : ℕ} (ht : 2 ≤ t)
    (v : Gram (windowLength k) → ℤ) (K : Set (Gram (windowLength k) → ℤ))
    (G : RuleSet k) (hgen : GeneratingAt v G)
    (hcat : ∀ u ∈ G, CatalogueRule t k u) (hK : ∀ u ∈ G, u ∈ K)
    (hsize : ∀ B ∈ blocks G, B.card ≤ windowLength k)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hnew : ∀ u ∈ G, w ≠ u ∧ w ≠ -u)
    (hspan : rational w ∈ Submodule.span ℚ (rational '' (↑G : Set _))) :
    ∃ U : RuleSet k, U ⊆ G ∧ Witness t k v K U := by sorry
