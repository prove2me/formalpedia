-- Prove2me | Theorems.Thm_DeletionCode_CatalogueBridge_catalogueGeneratingSet_card_bound
-- name    : DeletionCode.CatalogueBridge.catalogueGeneratingSet_card_bound
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:18:33.316484+00:00
-- url     : https://prove2.me/theorems/bb25116f-6488-480a-9bd4-2b0cd34fe449
-- title:
--   Catalogue Bridge: catalogue Generating Set card bound
-- statement:
--   The complete grammar-defined catalogue class inherits the finite-record count.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueBridge.lean#L115-L129
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueBridge.lean#L115-L129

import Definitions.Def_DeletionCode_CatalogueWords
import Definitions.Def_DeletionCode_SignedRuleCount
import Definitions.Def_DeletionCode_CatalogueBridge
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueBridge
open Windows HeaderRecovery CatalogueWords GeneratingModel SignedSupport
open RuleReconstruction SignedRuleCount DescriptionCount

theorem DeletionCode.CatalogueBridge.catalogueGeneratingSet_card_bound (x : Letters) (n k ν R t c : ℕ)
    (group : Fin ν → Fin R) (hν : 1 ≤ ν) (hx : KUnique x n k) :
    Nat.card {Q : RuleSet k // CatalogueGeneratingSet x n k ν R t c group Q} ≤
      n ^ c * (fieldBound (windowLength k) ν) ^ (50 * ν) := by sorry
