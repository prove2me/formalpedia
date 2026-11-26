-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_pair_eq_orderedContribution
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_pair_eq_orderedContribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:19:48.84528+00:00
-- url     : https://prove2.me/theorems/b0bf33da-0d53-4687-8eb7-f784eecd4116
-- title:
--   Forest: root Boundary Support Order Contribution pair eq ordered Contribution
-- statement:
--   The length-two root fiber follows the chosen first edge, then the chosen
--   second edge, and is exactly the corresponding ordered contribution.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L276-L359
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L276-L359

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_pair_eq_orderedContribution
    (choices : ActiveExtensionChoice V)
    (a b : Edge V) (ρ : (Edge V → ℝ) → ℝ)
    (hb :
      b ∈ (choices (Forest.empty V) (emptyActiveEdge a)).forest.activeEdges) :
    rootBoundarySupportOrderContribution choices ρ
        ((choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
          ⟨b, hb⟩).forest.support) [a, b] =
      (choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
        ⟨b, hb⟩).forest.orderedContribution [a, b] ρ := by sorry
