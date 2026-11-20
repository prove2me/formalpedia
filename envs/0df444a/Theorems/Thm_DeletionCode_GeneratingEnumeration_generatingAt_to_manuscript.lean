-- Prove2me | Theorems.Thm_DeletionCode_GeneratingEnumeration_generatingAt_to_manuscript
-- name    : DeletionCode.GeneratingEnumeration.generatingAt_to_manuscript
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:25:40.826183+00:00
-- url     : https://prove2.me/theorems/0a7dfd80-43f1-43c6-a7cd-78d45d9cd79e
-- title:
--   Generating Enumeration: generating At to manuscript
-- statement:
--   Finite ordered generation on actual catalogue vectors supplies the exact
--   concrete-presentation predicate counted by the manuscript theorem.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingEnumeration.lean#L217-L243
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingEnumeration.lean#L217-L243

import Definitions.Def_DeletionCode_FiniteGenerating
import Definitions.Def_DeletionCode_ManuscriptCounting
import Definitions.Def_DeletionCode_CatalogueFamily
import Mathlib.Data.Finset.Sort
import Definitions.Def_DeletionCode_GeneratingEnumeration
set_option autoImplicit true
open DeletionCode DeletionCode.GeneratingEnumeration
open Windows HeaderRecovery CatalogueWords CatalogueBridge GeneratingModel
open SignedSupport SignedRuleCount RuleReconstruction RuleSetGraph SupportComponents
open CanonicalIndex ConnectedBlocks FiniteGenerating
open scoped BigOperators

theorem DeletionCode.GeneratingEnumeration.generatingAt_to_manuscript {t k n : ℕ} (x : Letters) (G : RuleSet k)
    (hgen : GeneratingAt (wordSpectrum x n (windowLength k)) G)
    (hcat : ∀ w ∈ G, CatalogueRule t k w) :
    ManuscriptCounting.GeneratingSet t x n k G.card (componentCount G) G := by sorry
