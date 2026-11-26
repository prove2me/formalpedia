-- Prove2me | Theorems.Thm_BKAR_Forest_localRecursiveBoundaryRemainder_eq_sum_integral_child_sum_localBoundarySupportOrderContribution_add_localRecursiveBoundaryRemainder_of_allBranchesAnalytic
-- name    : BKAR.Forest.localRecursiveBoundaryRemainder_eq_sum_integral_child_sum_localBoundarySupportOrderContribution_add_localRecursiveBoundaryRemainder_of_allBranchesAnalytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:01.63454+00:00
-- url     : https://prove2.me/theorems/ab00a30c-0b6c-5d93-bda5-9a0ab6823429
-- title:
--   Forest: local Recursive Boundary Remainder eq sum integral child sum local Boundary Support Order Contribution add local Recursive Boundary Remainder of all Branches Analytic
-- statement:
--   One telescoping recurrence for the local recursive boundary remainder: each
--   child remainder splits into its local support/order boundary layer plus its
--   own recursive remainder.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L191-L237
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesTelescoping.lean#L191-L237

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.localRecursiveBoundaryRemainder_eq_sum_integral_child_sum_localBoundarySupportOrderContribution_add_localRecursiveBoundaryRemainder_of_allBranchesAnalytic
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    localRecursiveBoundaryRemainder choices F pref prefixTs top ρ =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          (Finset.sum (Finset.univ : Finset (ForestIndex V))
            (fun I => Finset.sum (edgeSetOrders I.edges)
              (fun order =>
                localBoundarySupportOrderContribution choices
                  (choices F e).forest (pref ++ [e.val])
                  (prefixTs ++ [t]) t I order ρ)) +
            localRecursiveBoundaryRemainder choices
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t ρ)) := by sorry
