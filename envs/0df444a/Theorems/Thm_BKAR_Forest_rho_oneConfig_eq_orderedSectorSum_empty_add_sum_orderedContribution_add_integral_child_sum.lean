-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_add_integral_child_sum
-- name    : BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_add_integral_child_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:17:03.350429+00:00
-- url     : https://prove2.me/theorems/a857890f-f511-4142-89a3-c6c4e27caa01
-- title:
--   Forest: rho one Config eq ordered Sector Sum empty add sum ordered Contribution add integral child sum
-- statement:
--   Root first-layer nonterminal regrouping bridge. Each first active edge now
--   contributes its one-edge ordered sector plus the exact recursive boundary
--   subtrees below the child.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L892-L939
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L892-L939

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_add_integral_child_sum
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hstd :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        IntervalIntegrable
          (fun t : ℝ =>
            mixedPartialList [e.val].reverse ρ
              ((choices (Forest.empty V) e).forest.standardInterp
                ((choices (Forest.empty V) e).forest.paramsOfOrder
                  [e.val] [t])))
          MeasureTheory.volume 0 1)
    (hrec :
      ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
        IntervalIntegrable
          (fun t : ℝ =>
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))
          MeasureTheory.volume 0 1) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e =>
            (choices (Forest.empty V) e).forest.orderedContribution
              [e.val] ρ +
            ∫ t in 0..(1 : ℝ),
              Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
                (fun e' => ∫ s in 0..t,
                  allBranchesBoundaryExpansion choices
                    (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                    (choices ((choices (Forest.empty V) e).forest) e').forest
                    ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ)) := by sorry
