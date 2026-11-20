-- Prove2me | Theorems.Thm_DeletionCode_CatalogueBridge_word_generating
-- name    : DeletionCode.CatalogueBridge.word_generating
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:28.486182+00:00
-- url     : https://prove2.me/theorems/877ebe8d-31b7-4467-bf04-99ecfeea3768
-- title:
--   Catalogue Bridge: word generating
-- statement:
--   Signed provenance supplies every actual negative L-window's source.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueBridge.lean#L71-L77
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueBridge.lean#L71-L77

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_CatalogueBridge
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount

theorem DeletionCode.CatalogueBridge.word_generating {k ν R n : ℕ} {x : Letters}
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R)
    (hvalid : ValidCatalogue bubbles group)
    (hgen : SignedGenerating (indexedFamily bubbles group).family x n (windowLength k)) :
    (indexedFamily bubbles group).family.Generating x n (windowLength k) := by sorry
