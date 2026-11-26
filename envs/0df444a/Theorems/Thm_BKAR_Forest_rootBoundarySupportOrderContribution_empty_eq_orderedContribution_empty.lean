-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:06:27.664071+00:00
-- url     : https://prove2.me/theorems/222a6d70-a79a-56d7-b9a8-3dbd704daee6
-- title:
--   Forest: root Boundary Support Order Contribution empty eq ordered Contribution empty
-- statement:
--   The Forest construction uses the root Boundary Support Order Contribution empty eq ordered Contribution empty property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L609-L617
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L609-L617

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_empty_eq_orderedContribution_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (I : ForestIndex V) (hI : I.edges = ∅) :
    rootBoundarySupportOrderContribution choices ρ I [] =
      (Forest.empty V).orderedContribution [] ρ := by sorry
