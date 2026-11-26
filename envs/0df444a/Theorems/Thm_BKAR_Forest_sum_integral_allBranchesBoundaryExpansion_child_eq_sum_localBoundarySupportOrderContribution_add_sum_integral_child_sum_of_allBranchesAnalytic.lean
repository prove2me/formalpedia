-- Prove2me | Theorems.Thm_BKAR_Forest_sum_integral_allBranchesBoundaryExpansion_child_eq_sum_localBoundarySupportOrderContribution_add_sum_integral_child_sum_of_allBranchesAnalytic
-- name    : BKAR.Forest.sum_integral_allBranchesBoundaryExpansion_child_eq_sum_localBoundarySupportOrderContribution_add_sum_integral_child_sum_of_allBranchesAnalytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:00:07.366728+00:00
-- url     : https://prove2.me/theorems/1d9e7e77-e56a-51b4-9826-8e0af4eb922c
-- title:
--   Forest: sum integral all Branches Boundary Expansion child eq sum local Boundary Support Order Contribution add sum integral child sum of all Branches Analytic
-- statement:
--   Arbitrary-node nonterminal regrouping step. After summing over all active
--   children, the first child sectors regroup by support and canonical order, and
--   the only remaining term is the exact recursive child-boundary sum.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L725-L783
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L725-L783

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_integral_allBranchesBoundaryExpansion_child_eq_sum_localBoundarySupportOrderContribution_add_sum_integral_child_sum_of_allBranchesAnalytic
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges) (hnodup : pref.Nodup)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          allBranchesBoundaryExpansion choices
            (choices F e).forest.activeEdges.card
            (choices F e).forest (pref ++ [e.val])
            (prefixTs ++ [t]) t ρ) =
      Finset.sum (Finset.univ : Finset (ForestIndex V))
        (fun I => Finset.sum (edgeSetOrders I.edges)
          (fun order =>
            localBoundarySupportOrderContribution choices F pref prefixTs top
              I order ρ)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            Finset.sum (choices F e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices (choices F e).forest e').forest.activeEdges.card
                  (choices (choices F e).forest e').forest
                  ((pref ++ [e.val]) ++ [e'.val])
                  ((prefixTs ++ [t]) ++ [s]) s ρ)) := by sorry
