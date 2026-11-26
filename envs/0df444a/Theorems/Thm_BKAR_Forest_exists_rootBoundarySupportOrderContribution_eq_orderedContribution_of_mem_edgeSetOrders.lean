-- Prove2me | Theorems.Thm_BKAR_Forest_exists_rootBoundarySupportOrderContribution_eq_orderedContribution_of_mem_edgeSetOrders
-- name    : BKAR.Forest.exists_rootBoundarySupportOrderContribution_eq_orderedContribution_of_mem_edgeSetOrders
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:54:32.223384+00:00
-- url     : https://prove2.me/theorems/63d2dc90-38a2-404f-a618-e55a245a4bb0
-- title:
--   Forest: exists root Boundary Support Order Contribution eq ordered Contribution of mem edge Set Orders
-- statement:
--   For a canonical support order, the root fiber is an ordered sector of the
--   `Forest` representative grown by following that order. This isolates the only remaining
--   choice dependence in the sector integrand: the grown `Forest` representative data.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L136-L165
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L136-L165

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.exists_rootBoundarySupportOrderContribution_eq_orderedContribution_of_mem_edgeSetOrders
    (choices : ActiveExtensionChoice V)
    {I : ForestIndex V} {order : List (Edge V)}
    (horder : order ∈ edgeSetOrders I.edges)
    (ρ : (Edge V → ℝ) → ℝ) :
    ∃ G : Forest V, G.support = I ∧
      rootBoundarySupportOrderContribution choices ρ I order =
        G.orderedContribution order ρ := by sorry
