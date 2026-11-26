-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_supportOrderContribution
-- name    : BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_supportOrderContribution
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:45:14.981455+00:00
-- url     : https://prove2.me/theorems/f672e97b-bf31-510a-9637-ae7c27ae7d97
-- title:
--   Forest: rho one Config eq ordered Sector Sum empty add singleton support Order Contribution
-- statement:
--   Root terminal-child base case, already regrouped by finite support and
--   canonical edge order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L1117-L1138
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L1117-L1138

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_supportOrderContribution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hterm : ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        Finset.sum (Finset.univ : Finset (ForestIndex V))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              ActiveTerminalBranchData.supportOrderContribution
                (ActiveTerminalBranchData.singleton
                  (fun e => choices (Forest.empty V) e) hterm)
                I order ρ)) := by sorry
