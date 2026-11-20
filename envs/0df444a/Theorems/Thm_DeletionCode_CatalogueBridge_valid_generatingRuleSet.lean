-- Prove2me | Theorems.Thm_DeletionCode_CatalogueBridge_valid_generatingRuleSet
-- name    : DeletionCode.CatalogueBridge.valid_generatingRuleSet
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:16.282184+00:00
-- url     : https://prove2.me/theorems/f8af2a78-0fb1-4fb0-be46-4a5c43efebde
-- title:
--   Catalogue Bridge: valid generating Rule Set
-- statement:
--   The concrete catalogue conditions imply the entire signed counting interface.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueBridge.lean#L80-L88
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueBridge.lean#L80-L88

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_CatalogueBridge
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount

theorem DeletionCode.CatalogueBridge.valid_generatingRuleSet {k ν R n c : ℕ} {x : Letters}
    (bubbles : Fin ν → BubbleWord k) (group : Fin ν → Fin R)
    (hvalid : ValidCatalogue bubbles group)
    (hgen : SignedGenerating (indexedFamily bubbles group).family x n (windowLength k))
    (hc : Fintype.card
      (SupportComponents.GraphComponents (indexedFamily bubbles group).family (windowLength k)) = c) :
    GeneratingRuleSet x n k ν R c group (rulesOfFamily (indexedFamily bubbles group) group) := by sorry
