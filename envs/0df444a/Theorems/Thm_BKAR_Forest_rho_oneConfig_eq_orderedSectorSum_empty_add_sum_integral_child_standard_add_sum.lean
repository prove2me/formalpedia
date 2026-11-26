-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_integral_child_standard_add_sum
-- name    : BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_integral_child_standard_add_sum
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:44:42.143795+00:00
-- url     : https://prove2.me/theorems/8a8033ea-09fc-47f6-ab2b-83266eeaca07
-- title:
--   Forest: rho one Config eq ordered Sector Sum empty add sum integral child standard add sum
-- statement:
--   Root boundary-tree identity with every first child unfolded once. The
--   recursive grandchildren are still exact-depth boundary subtrees.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L925-L953
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L925-L953

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_integral_child_standard_add_sum
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            (mixedPartialList [e.val].reverse ρ
              ((choices (Forest.empty V) e).forest.standardInterp
                ((choices (Forest.empty V) e).forest.paramsOfOrder
                  [e.val] [t])) +
            Finset.sum (choices (Forest.empty V) e).forest.activeEdges.attach
              (fun e' => ∫ s in 0..t,
                allBranchesBoundaryExpansion choices
                  (choices ((choices (Forest.empty V) e).forest) e').forest.activeEdges.card
                  (choices ((choices (Forest.empty V) e).forest) e').forest
                  ([e.val] ++ [e'.val]) ([t] ++ [s]) s ρ))) := by sorry
