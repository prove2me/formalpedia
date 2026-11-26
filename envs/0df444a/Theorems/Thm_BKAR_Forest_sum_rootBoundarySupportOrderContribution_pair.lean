-- Prove2me | Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_pair
-- name    : BKAR.Forest.sum_rootBoundarySupportOrderContribution_pair
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:01:00.993723+00:00
-- url     : https://prove2.me/theorems/15549683-26f7-5c36-9e2d-0ad1e1fd17f4
-- title:
--   Forest: sum root Boundary Support Order Contribution pair
-- statement:
--   After summing over all support indices, a fixed active two-edge order leaves
--   only the support grown by the corresponding two chosen extensions.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L365-L408
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L365-L408

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_rootBoundarySupportOrderContribution_pair
    (choices : ActiveExtensionChoice V)
    (a b : Edge V) (ρ : (Edge V → ℝ) → ℝ)
    (hb :
      b ∈ (choices (Forest.empty V) (emptyActiveEdge a)).forest.activeEdges) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I [a, b]) =
      (choices (choices (Forest.empty V) (emptyActiveEdge a)).forest
        ⟨b, hb⟩).forest.orderedContribution [a, b] ρ := by sorry
