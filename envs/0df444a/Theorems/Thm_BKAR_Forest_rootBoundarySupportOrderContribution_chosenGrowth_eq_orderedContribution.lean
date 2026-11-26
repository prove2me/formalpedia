-- Prove2me | Theorems.Thm_BKAR_Forest_rootBoundarySupportOrderContribution_chosenGrowth_eq_orderedContribution
-- name    : BKAR.Forest.rootBoundarySupportOrderContribution_chosenGrowth_eq_orderedContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:07:31.044857+00:00
-- url     : https://prove2.me/theorems/2e8935c1-ac8d-5d59-a017-0884b5d97f2f
-- title:
--   Forest: root Boundary Support Order Contribution chosen Growth eq ordered Contribution
-- statement:
--   Root specialization of
--   `boundarySupportOrderTreeFiber_chosenGrowth_eq_orderedSimplexIntegralAux`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L566-L582
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/Core.lean#L566-L582

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_FollowOrder
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rootBoundarySupportOrderContribution_chosenGrowth_eq_orderedContribution
    (choices : ActiveExtensionChoice V)
    {G : Forest V} {order : List (Edge V)}
    (path : ChosenGrowth choices (Forest.empty V) order G)
    (ρ : (Edge V → ℝ) → ℝ)
    (horder : order ≠ []) :
    rootBoundarySupportOrderContribution choices ρ G.support order =
      G.orderedContribution order ρ := by sorry
