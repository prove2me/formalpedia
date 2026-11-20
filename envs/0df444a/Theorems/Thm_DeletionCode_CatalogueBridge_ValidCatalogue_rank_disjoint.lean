-- Prove2me | Theorems.Thm_DeletionCode_CatalogueBridge_ValidCatalogue_rank_disjoint
-- name    : DeletionCode.CatalogueBridge.ValidCatalogue.rank_disjoint
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:13.566623+00:00
-- url     : https://prove2.me/theorems/e15420de-e165-4d42-87d0-1c937e46e5f3
-- title:
--   Valid Catalogue: rank disjoint
-- statement:
--   The Valid Catalogue construction uses the rank disjoint property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueBridge.lean#L57-L68
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueBridge.lean#L57-L68

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_CatalogueBridge
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount

theorem DeletionCode.CatalogueBridge.ValidCatalogue.rank_disjoint {k ν R : ℕ}
    {bubbles : Fin ν → BubbleWord k} {group : Fin ν → Fin R}
    (h : ValidCatalogue bubbles group) :
    ∀ i, VertexDisjointOn (indexedFamily bubbles group).family (windowLength k)
      (ruleBubbles (indexedFamily bubbles group).family i) := by sorry
