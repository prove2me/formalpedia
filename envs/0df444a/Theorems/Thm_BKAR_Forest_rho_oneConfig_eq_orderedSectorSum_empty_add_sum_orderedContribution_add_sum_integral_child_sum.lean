-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_add_sum_integral_child_sum
-- name    : BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_add_sum_integral_child_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:16:38.836885+00:00
-- url     : https://prove2.me/theorems/046a9d3c-ae55-5354-97bc-3dadc6f072c0
-- title:
--   Forest: rho one Config eq ordered Sector Sum empty add sum ordered Contribution add sum integral child sum
-- statement:
--   Separated finite-sum form of the root nonterminal bridge: exposed one-edge
--   sectors and recursive child sums are now two distinct finite sums.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L945-L987
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L945-L987

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_orderedContribution_add_sum_integral_child_sum
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
        (Finset.sum (Forest.empty V).activeEdges.attach
          (fun e =>
            (choices (Forest.empty V) e).forest.orderedContribution
              [e.val] ρ) +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))) := by sorry
