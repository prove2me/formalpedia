-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_allBranchesExpansion_empty
-- name    : BKAR.Forest.rho_oneConfig_eq_allBranchesExpansion_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:34.937022+00:00
-- url     : https://prove2.me/theorems/24e9a47b-3ee5-43b2-bc90-12473dba9064
-- title:
--   Forest: rho one Config eq all Branches Expansion empty
-- statement:
--   Root form of the all-branches induction, specialized to the empty forest and
--   the all-one endpoint.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L767-L778
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L767-L778

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_allBranchesExpansion_empty
    (choices : ActiveExtensionChoice V) (n : Nat)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices n (Forest.empty V) [] [] 1 ρ) :
    ρ oneConfig =
      allBranchesExpansion choices n (Forest.empty V) [] [] 1 ρ := by sorry
