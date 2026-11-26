-- Prove2me | Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_empty_child_eq_orderedContribution_add_integral_sum
-- name    : BKAR.Forest.integral_allBranchesBoundaryExpansion_empty_child_eq_orderedContribution_add_integral_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:35.116796+00:00
-- url     : https://prove2.me/theorems/325c3113-8812-5c63-8640-8a02127c71ff
-- title:
--   Forest: integral all Branches Boundary Expansion empty child eq ordered Contribution add integral sum
-- statement:
--   Empty-start form of the nonterminal child split: the first child sector is the
--   one-edge ordered contribution of the child forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L822-L885
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L822-L885

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_allBranchesBoundaryExpansion_empty_child_eq_orderedContribution_add_integral_sum
    (choices : ActiveExtensionChoice V)
    (e : {e // e ∈ (Forest.empty V).activeEdges})
    (ρ : (Edge V → ℝ) → ℝ)
    (hstd :
      IntervalIntegrable
        (fun t : ℝ =>
          mixedPartialList [e.val].reverse ρ
            ((choices (Forest.empty V) e).forest.standardInterp
              ((choices (Forest.empty V) e).forest.paramsOfOrder
                [e.val] [t])))
        MeasureTheory.volume 0 1)
    (hrec :
      IntervalIntegrable
        (fun t : ℝ =>
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))
        MeasureTheory.volume 0 1) :
    (∫ t in 0..(1 : ℝ),
        allBranchesBoundaryExpansion choices
          (choices (Forest.empty V) e).forest.activeEdges.card
          (choices (Forest.empty V) e).forest [e.val] [t] t ρ) =
      (choices (Forest.empty V) e).forest.orderedContribution [e.val] ρ +
        ∫ t in 0..(1 : ℝ),
          Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                (choices ((choices (Forest.empty V) e).forest) e').forest
                ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ) := by sorry
