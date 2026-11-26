-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_localBoundarySupportOrderContribution_empty_add_sum_integral_child_sum
-- name    : BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_localBoundarySupportOrderContribution_empty_add_sum_integral_child_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:17:31.249496+00:00
-- url     : https://prove2.me/theorems/93441d07-5ae9-45bd-a9e8-215a5f8432ed
-- title:
--   Forest: rho one Config eq ordered Sector Sum empty add sum local Boundary Support Order Contribution empty add sum integral child sum
-- statement:
--   Root specialization of the arbitrary-node nonterminal regrouping step.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L788-L816
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L788-L816

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_localBoundarySupportOrderContribution_empty_add_sum_integral_child_sum
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
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))) := by sorry
