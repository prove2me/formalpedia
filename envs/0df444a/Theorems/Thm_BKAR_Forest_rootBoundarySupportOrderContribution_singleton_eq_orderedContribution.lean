-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_singleton_eq_orderedContribution
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_singleton_eq_orderedContribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:07:20.965044+00:00
-- url     : https://prove2.me/theorems/8be508de-8f2d-4b75-8b90-f3574377de41
-- title:
--   Forest: root Boundary Support Order Contribution singleton eq ordered Contribution
-- statement:
--   The Forest construction uses the root Boundary Support Order Contribution singleton eq ordered Contribution property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L650-L688
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L650-L688

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_singleton_eq_orderedContribution
    (choices : ActiveExtensionChoice V)
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    rootBoundarySupportOrderContribution choices ρ (ForestIndex.singleton a) [a] =
      (choices (Forest.empty V) (emptyActiveEdge a)).forest.orderedContribution
        [a] ρ := by sorry
