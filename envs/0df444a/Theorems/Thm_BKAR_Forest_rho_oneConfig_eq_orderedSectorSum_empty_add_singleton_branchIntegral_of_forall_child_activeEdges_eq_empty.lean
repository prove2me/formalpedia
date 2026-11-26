-- Prove2me | Theorems.Thm_BKAR_Forest_rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_branchIntegral_of_forall_child_activeEdges_eq_empty
-- name    : BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_branchIntegral_of_forall_child_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:15:25.329177+00:00
-- url     : https://prove2.me/theorems/aa5ba182-cb79-48f2-af49-5f1a17ff43e3
-- title:
--   Forest: rho one Config eq ordered Sector Sum empty add singleton branch Integral of forall child active Edges eq empty
-- statement:
--   Root terminal-child base case, expressed through the singleton
--   `ActiveTerminalBranchData` branch sum.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L1086-L1111
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L1086-L1111

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.rho_oneConfig_eq_orderedSectorSum_empty_add_singleton_branchIntegral_of_forall_child_activeEdges_eq_empty
    (choices : ActiveExtensionChoice V)
    (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices (Forest.empty V).activeEdges.card
        (Forest.empty V) [] [] 1 ρ)
    (hterm : ∀ e : {e // e ∈ (Forest.empty V).activeEdges},
      (choices (Forest.empty V) e).forest.activeEdges = ∅) :
    ρ oneConfig =
      (Forest.empty V).orderedSectorSum ρ +
        (ActiveTerminalBranchData.singleton
          (fun e => choices (Forest.empty V) e) hterm).branchIntegral
            emptyParam ρ := by sorry
