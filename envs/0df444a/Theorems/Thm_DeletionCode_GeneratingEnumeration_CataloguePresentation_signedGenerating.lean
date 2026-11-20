-- Prove2me | Theorems.Thm_DeletionCode_GeneratingEnumeration_CataloguePresentation_signedGenerating
-- name    : DeletionCode.GeneratingEnumeration.CataloguePresentation.signedGenerating
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:25:25.555172+00:00
-- url     : https://prove2.me/theorems/3e44592d-8241-49f3-9ff5-4d61390bdf9b
-- title:
--   Catalogue Presentation: signed Generating
-- statement:
--   The concrete chosen presentation inherits exactly the earlier-rule suppliers.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingEnumeration.lean#L183-L213
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingEnumeration.lean#L183-L213

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

theorem DeletionCode.GeneratingEnumeration.CataloguePresentation.signedGenerating {t k R : ℕ}
    {rules : Fin R → Gram (windowLength k) → ℤ} (P : CataloguePresentation t k R rules)
    (x : Letters) (n : ℕ)
    (hgen : ∀ i g, rules i g = -1 → wordSpectrum x n (windowLength k) g ≠ 0 ∨
      ∃ j : Fin R, j < i ∧ rules j g ≠ 0) :
    SignedGenerating (flatFamily t R P.words).family x n (windowLength k) := by sorry
