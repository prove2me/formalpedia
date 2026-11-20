-- Prove2me | Theorems.Thm_DeletionCode_GeneratingEnumeration_rank_sorted_enumeration
-- name    : DeletionCode.GeneratingEnumeration.rank_sorted_enumeration
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:25:36.65999+00:00
-- url     : https://prove2.me/theorems/c21accfc-63c4-4224-832f-8d891ef44c0a
-- title:
--   Generating Enumeration: rank sorted enumeration
-- statement:
--   Sort the actual finite set by its injective ranks.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingEnumeration.lean#L22-L48
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/GeneratingEnumeration.lean#L22-L48

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

theorem DeletionCode.GeneratingEnumeration.rank_sorted_enumeration {k : ℕ} (G : RuleSet k)
    (rank : (Gram (windowLength k) → ℤ) → ℕ)
    (hinj : Set.InjOn rank (↑G : Set _)) :
    ∃ e : Fin G.card ≃ G, StrictMono (fun i => rank (e i).val) := by sorry
