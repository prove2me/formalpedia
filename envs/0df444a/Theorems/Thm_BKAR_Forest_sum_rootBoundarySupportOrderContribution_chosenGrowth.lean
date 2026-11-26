-- Prove2me | Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_chosenGrowth
-- name    : BKAR.Forest.sum_rootBoundarySupportOrderContribution_chosenGrowth
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:19:33.253657+00:00
-- url     : https://prove2.me/theorems/a87507dd-cea2-4ae3-8305-eb1fb6f49cd1
-- title:
--   Forest: sum root Boundary Support Order Contribution chosen Growth
-- statement:
--   For any chosen root growth path, summing the fixed order over all support
--   indices leaves exactly the ordered contribution of the path's terminal forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L58-L85
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L58-L85

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_rootBoundarySupportOrderContribution_chosenGrowth
    (choices : ActiveExtensionChoice V)
    {G : Forest V} {order : List (Edge V)}
    (path : ChosenGrowth choices (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => rootBoundarySupportOrderContribution choices ρ I order) =
      G.orderedContribution order ρ := by sorry
