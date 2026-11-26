-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_localBoundarySupportOrderContribution_empty_add_localRecursiveBoundaryRemainder
-- name    : BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_localBoundarySupportOrderContribution_empty_add_localRecursiveBoundaryRemainder
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:17:08.227875+00:00
-- url     : https://prove2.me/theorems/b823000b-74ee-5c41-a8a3-dec063e57c77
-- title:
--   Forest: rho one Config eq ordered Sector Sum empty add sum local Boundary Support Order Contribution empty add local Recursive Boundary Remainder
-- statement:
--   Root exact boundary-tree regrouping with the remaining recursive contribution
--   expressed by the local remainder API.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L409-L426
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L409-L426

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_localBoundarySupportOrderContribution_empty_add_localRecursiveBoundaryRemainder
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
              localBoundarySupportOrderContribution choices
                (Forest.empty V) [] [] 1 I order ρ)) +
          localRecursiveBoundaryRemainder choices (Forest.empty V) [] [] 1 ρ) := by sorry
