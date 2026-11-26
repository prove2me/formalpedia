-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_nontrivialIntegrable
-- name    : BKAR.Forest.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_nontrivialIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:18:10.783795+00:00
-- url     : https://prove2.me/theorems/ecf7816a-3e68-4bb0-b853-0e2a889090a8
-- title:
--   Forest: rho one Config eq zero Config add sum boundary Support Order Tree Fiber filter edges ne empty of nontrivial Integrable
-- statement:
--   Root identity whose remaining analytic side condition is restricted to the
--   nontrivial support/order fibers.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L856-L879
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesFibers.lean#L856-L879

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesTelescoping
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFibers
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_zeroConfig_add_sum_boundarySupportOrderTreeFiber_filter_edges_ne_empty_of_nontrivialIntegrable
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hfiber :
      boundarySupportOrderTreeFiberNontrivialIntegrable choices
        (Forest.empty V).activeEdges.card (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      ρ zeroConfig +
        Finset.sum
          ((Finset.univ : Finset (ForestIndex V)).filter
            (fun I => I.edges ≠ ∅))
          (fun I => Finset.sum (edgeSetOrders I.edges)
            (fun order =>
              boundarySupportOrderTreeFiber choices (Forest.empty V) [] [] 1
                I order ρ)) := by sorry
