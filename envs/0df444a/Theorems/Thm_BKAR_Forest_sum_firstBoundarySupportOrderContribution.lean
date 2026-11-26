-- Prove2me | Theorems.Thm_BKAR_Forest_sum_firstBoundarySupportOrderContribution
-- name    : BKAR.Forest.sum_firstBoundarySupportOrderContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:35.996109+00:00
-- url     : https://prove2.me/theorems/bb3a2567-6b33-454d-8be7-bdef555fcd6c
-- title:
--   Forest: sum first Boundary Support Order Contribution
-- statement:
--   Exposed first boundary sectors regroup by support and canonical order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L466-L480
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L466-L480

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_firstBoundarySupportOrderContribution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum (Forest.empty V).activeEdges.attach
        (fun e =>
          (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            firstBoundarySupportOrderContribution choices I order ρ)) := by sorry
