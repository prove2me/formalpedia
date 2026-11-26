-- Prove2me | Theorems.Thm_BKAR_Forest_exists_sum_rootBoundarySupportOrderContribution_eq_orderedContribution_of_mem_edgeSetOrders
-- name    : BKAR.Forest.exists_sum_rootBoundarySupportOrderContribution_eq_orderedContribution_of_mem_edgeSetOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:56:27.741882+00:00
-- url     : https://prove2.me/theorems/f2fa4e2d-ba33-55bd-aec4-2a231375c006
-- title:
--   Forest: exists sum root Boundary Support Order Contribution eq ordered Contribution of mem edge Set Orders
-- statement:
--   After summing over all support indices, a canonical order leaves the ordered
--   sector of the `Forest` representative grown by following that order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L171-L186
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L171-L186

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.exists_sum_rootBoundarySupportOrderContribution_eq_orderedContribution_of_mem_edgeSetOrders
    (choices : ActiveExtensionChoice V)
    {I : ForestIndex V} {order : List (Edge V)}
    (horder : order ∈ edgeSetOrders I.edges)
    (ρ : (Edge V → ℝ) → ℝ) :
    ∃ G : Forest V, G.support = I ∧
      Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun J => rootBoundarySupportOrderContribution choices ρ J order) =
        G.orderedContribution order ρ := by sorry
