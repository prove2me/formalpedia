-- Prove2me | Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_eq_terminalSingletonBranchIntegralAux
-- name    : BKAR.Forest.integral_allBranchesBoundaryExpansion_eq_terminalSingletonBranchIntegralAux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:14:40.268551+00:00
-- url     : https://prove2.me/theorems/53bda175-3a1b-5221-b3c5-bb384b9a08a1
-- title:
--   Forest: integral all Branches Boundary Expansion eq terminal Singleton Branch Integral Aux
-- statement:
--   A terminal child of the all-branches boundary tree is the singleton terminal
--   branch integral already used by the ordered-assembly API.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L981-L1024
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L981-L1024

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_allBranchesBoundaryExpansion_eq_terminalSingletonBranchIntegralAux
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : (choices F e).forest.activeEdges = ∅) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val]) (prefixTs ++ [t]) t ρ) =
      (TerminalGrowth.cons (choices F e)
          (TerminalGrowth.ofActiveEdgesEqEmpty
            (choices F e).forest hterm)).branchIntegralAux top
        (F.paramsOfOrder pref prefixTs) (mixedPartialList pref.reverse ρ) := by sorry
