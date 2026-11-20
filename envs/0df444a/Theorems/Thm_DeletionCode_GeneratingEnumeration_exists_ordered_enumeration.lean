-- Prove2me | Theorems.Thm_DeletionCode_GeneratingEnumeration_exists_ordered_enumeration
-- name    : DeletionCode.GeneratingEnumeration.exists_ordered_enumeration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:25:37.355224+00:00
-- url     : https://prove2.me/theorems/96f16cdf-a169-4bd8-91f9-0057a3602293
-- title:
--   Generating Enumeration: exists ordered enumeration
-- statement:
--   The earlier-supplier property survives the rank-sorted finite enumeration.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingEnumeration.lean#L51-L70
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingEnumeration.lean#L51-L70

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

theorem DeletionCode.GeneratingEnumeration.exists_ordered_enumeration {k : ℕ} (v : Gram (windowLength k) → ℤ)
    (G : RuleSet k) (hgen : GeneratingAt v G) :
    ∃ e : Fin G.card ≃ G, ∀ i g, (e i).val g = -1 →
      v g ≠ 0 ∨ ∃ j : Fin G.card, j < i ∧ (e j).val g ≠ 0 := by sorry
