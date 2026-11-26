-- Prove2me | Theorems.Thm_BKAR_Forest_sum_rootBoundarySupportOrderContribution_singletonSupport
-- name    : BKAR.Forest.sum_rootBoundarySupportOrderContribution_singletonSupport
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:57:30.117776+00:00
-- url     : https://prove2.me/theorems/b390447a-6aca-4c16-8614-0ab6d580f27c
-- title:
--   Forest: sum root Boundary Support Order Contribution singleton Support
-- statement:
--   The singleton support inner sum has already collapsed to the unique singleton
--   order and is the matching one-edge ordered contribution.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L258-L270
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFiberBridge/LowRank.lean#L258-L270

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_Core
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberBridge_LowRank
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_rootBoundarySupportOrderContribution_singletonSupport
    (choices : ActiveExtensionChoice V)
    (a : Edge V) (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (edgeSetOrders (ForestIndex.singleton a : ForestIndex V).edges)
        (fun order =>
          rootBoundarySupportOrderContribution choices ρ
            (ForestIndex.singleton a) order) =
      (choices (Forest.empty V) (emptyActiveEdge a)).forest.orderedContribution
        [a] ρ := by sorry
