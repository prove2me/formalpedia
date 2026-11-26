-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum_localBoundarySupportOrderContribution_add_localRecursiveBoundaryRemainder
-- name    : BKAR.Forest.allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum_localBoundarySupportOrderContribution_add_localRecursiveBoundaryRemainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:37.108174+00:00
-- url     : https://prove2.me/theorems/08ce67c6-d4da-4b0b-b57d-d283c3b20c96
-- title:
--   Forest: all Branches Boundary Expansion active Edges card eq standard add sum local Boundary Support Order Contribution add local Recursive Boundary Remainder
-- statement:
--   Exact one-step support/order regrouping of the boundary tree at an arbitrary
--   node.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L354-L375
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L354-L375

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesBoundaryExpansion_activeEdges_card_eq_standard_add_sum_localBoundarySupportOrderContribution_add_localRecursiveBoundaryRemainder
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        (Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              localBoundarySupportOrderContribution choices F pref prefixTs
                top I order ρ)) +
          localRecursiveBoundaryRemainder choices F pref prefixTs top ρ) := by sorry
