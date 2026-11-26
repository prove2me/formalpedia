-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
-- name    : BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:57:25.115794+00:00
-- url     : https://prove2.me/theorems/ec8579a7-cb35-505d-a717-c56ec936d27c
-- title:
--   Forest: rho one Config eq ordered Sector Sum empty add sum all Branches Boundary Expansion
-- statement:
--   Root exact-depth recursion in boundary-sector form: the BKAR value is the empty
--   sector plus the exact-depth boundary trees below each first active edge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L802-L819
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L802-L819

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_sum_allBranchesBoundaryExpansion
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        Finset.sum (Forest.empty V).activeEdges.attach
          (fun e => ∫ t in 0..(1 : ℝ),
            allBranchesBoundaryExpansion choices
              (choices (Forest.empty V) e).forest.activeEdges.card
              (choices (Forest.empty V) e).forest [e.val] [t] t ρ) := by sorry
