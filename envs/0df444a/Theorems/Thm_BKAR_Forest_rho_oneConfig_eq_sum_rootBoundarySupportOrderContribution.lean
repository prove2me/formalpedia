-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution
-- name    : BKAR.Forest.rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:18:03.085069+00:00
-- url     : https://prove2.me/theorems/31c29934-a166-5e0e-844f-b030f199f9b7
-- title:
--   Forest: rho one Config eq sum root Boundary Support Order Contribution
-- statement:
--   Root BKAR identity with the folded boundary tree flattened into the final
--   global support/order sector sum. The empty support/order sector contributes
--   `ρ zeroConfig`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L803-L824
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L803-L824

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_sum_rootBoundarySupportOrderContribution
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hfiber :
      boundarySupportOrderTreeFiberIntegrable choices
        (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            rootBoundarySupportOrderContribution choices ρ I order)) := by sorry
