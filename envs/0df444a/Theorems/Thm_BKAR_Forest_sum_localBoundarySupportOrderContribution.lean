-- Prove2me | Theorems.Thm_BKAR_Forest_sum_localBoundarySupportOrderContribution
-- name    : BKAR.Forest.sum_localBoundarySupportOrderContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:10.871386+00:00
-- url     : https://prove2.me/theorems/7ff20609-cd3f-449a-82e1-307fb5185dd3
-- title:
--   Forest: sum local Boundary Support Order Contribution
-- statement:
--   Local active-boundary sectors regroup by child support and order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L274-L296
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L274-L296

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_localBoundarySupportOrderContribution
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (ρ : (Edge V → ℝ) → ℝ) :
    Finset.sum F.activeEdges.attach
        (fun e =>
          orderedSimplexIntegralAux top [e.val]
            (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
              ((choices F e).forest.standardInterp
                ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                  (prefixTs ++ ts))))) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            localBoundarySupportOrderContribution choices F pref prefixTs top
              I order ρ)) := by sorry
