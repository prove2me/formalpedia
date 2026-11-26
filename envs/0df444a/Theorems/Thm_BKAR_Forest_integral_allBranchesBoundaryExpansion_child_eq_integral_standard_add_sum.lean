-- Prove2me | Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_sum
-- name    : BKAR.Forest.integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:58:42.7261+00:00
-- url     : https://prove2.me/theorems/3d66f6e4-4406-5b0a-91ea-e6963ed0c48a
-- title:
--   Forest: integral all Branches Boundary Expansion child eq integral standard add sum
-- statement:
--   Unfold one child exact-depth boundary subtree under its parent integral. This
--   is the nonterminal regrouping shape before applying interval-integral
--   linearity.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L856-L883
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L856-L883

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_sum
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ) =
      ∫ t in 0..top,
        (mixedPartialList (pref ++ [e.val]).reverse ρ
          ((choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
              (prefixTs ++ [t]))) +
        Finset.sum (choices F e).forest.activeEdges.attach
          (fun e' => ∫ s in 0..t,
            allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ)) := by sorry
