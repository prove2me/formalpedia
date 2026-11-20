-- Prove2me | Theorems.Thm_DeletionCode_CatalogueAlgebra_new_relation_support
-- name    : DeletionCode.CatalogueAlgebra.new_relation_support
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-19T06:23:48.652898+00:00
-- url     : https://prove2.me/theorems/a1951b12-7c5a-4fdd-9a1f-6a4bb841a97d
-- title:
--   Catalogue Algebra: new relation support
-- statement:
--   Removing zero coefficients gives a genuine finite relation; novelty up to
--   sign forces at least two participating rules.
--
--   Source: https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueAlgebra.lean#L61-L115
-- source:
--   https://github.com/eengad/deletion-codes-lean/blob/24d093a4db95895a7206d8a23dbe2d7922258701/DeletionCode/CatalogueAlgebra.lean#L61-L115

import Definitions.Def_DeletionCode_RelationSavings
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Definitions.Def_DeletionCode_CatalogueAlgebra
set_option autoImplicit true
open DeletionCode DeletionCode.CatalogueAlgebra
open HeaderRecovery SignedSupport SignedRuleCount RuleSetGraph ConnectedBlocks CatalogueBridge
open scoped BigOperators

theorem DeletionCode.CatalogueAlgebra.new_relation_support {t k : ℕ} (ht : 1 ≤ t) (G : RuleSet k)
    (hcat : ∀ u ∈ G, CatalogueRule t k u)
    (w : Gram (windowLength k) → ℤ) (hw : CatalogueRule t k w)
    (hnew : ∀ u ∈ G, w ≠ u ∧ w ≠ -u)
    (hspan : rational w ∈ Submodule.span ℚ (rational '' (↑G : Set _))) :
    ∃ I : RuleSet k, I ⊆ G ∧ 2 ≤ I.card ∧
      ∃ a : (Gram (windowLength k) → ℤ) → ℚ,
        (∀ u ∈ I, a u ≠ 0) ∧
        ∀ g, (w g : ℚ) = ∑ u ∈ I, a u * (u g : ℚ) := by sorry
