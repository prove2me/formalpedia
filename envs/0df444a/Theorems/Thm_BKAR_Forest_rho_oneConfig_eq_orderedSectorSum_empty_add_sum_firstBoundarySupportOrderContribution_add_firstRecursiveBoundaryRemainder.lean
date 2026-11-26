-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_firstBoundarySupportOrderContribution_add_firstRecursiveBoundaryRemainder
-- name    : BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_firstBoundarySupportOrderContribution_add_firstRecursiveBoundaryRemainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:38.360796+00:00
-- url     : https://prove2.me/theorems/41c9a300-c4fc-599a-adaa-10648cacc3e5
-- title:
--   Forest: rho one Config eq ordered Sector Sum empty add sum first Boundary Support Order Contribution add first Recursive Boundary Remainder
-- statement:
--   Root nonterminal regrouping with the recursive contribution packaged as the
--   first recursive boundary remainder.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L1056-L1071
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L1056-L1071

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_firstBoundarySupportOrderContribution_add_firstRecursiveBoundaryRemainder
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              firstBoundarySupportOrderContribution choices I order ρ)) +
        firstRecursiveBoundaryRemainder choices ρ) := by sorry
