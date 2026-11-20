-- Prove2me | Theorems.Thm_DeletionCode_WitnessCases_relation_hull_card
-- name    : DeletionCode.WitnessCases.relation_hull_card
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:25:31.4322+00:00
-- url     : https://prove2.me/theorems/d280d76f-a2f6-4bdb-9812-013a633245f7
-- title:
--   Witness Cases: relation hull card
-- statement:
--   The Witness Cases construction uses the relation hull card property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCases.lean#L49-L67
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/WitnessCases.lean#L49-L67

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

theorem DeletionCode.WitnessCases.relation_hull_card {t k : ℕ} (G I : RuleSet k) (hIG : I ⊆ G)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (a : (Gram (windowLength k) → ℤ) → ℚ) (hind : Independent G)
    (ha : ∀ u ∈ I, a u ≠ 0)
    (hrel : ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ))
    (hsize : ∀ B ∈ blocks G, B.card ≤ windowLength k) :
    (RelationBlockSavings.blockHull G I).card ≤ 2 * t * windowLength k := by sorry
