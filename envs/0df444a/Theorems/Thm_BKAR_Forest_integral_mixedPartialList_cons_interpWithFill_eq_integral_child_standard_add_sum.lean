-- Prove2me | Theorems.Thm_BKAR_Forest_integral_mixedPartialList_cons_interpWithFill_eq_integral_child_standard_add_sum
-- name    : BKAR.Forest.integral_mixedPartialList_cons_interpWithFill_eq_integral_child_standard_add_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:44:35.242163+00:00
-- url     : https://prove2.me/theorems/72bdb97b-9eb2-5f69-8120-e6f02df2b604
-- title:
--   Forest: integral mixed Partial List cons interp With Fill eq integral child standard add sum
-- statement:
--   One active-edge summand, after exact-depth all-branches expansion below that
--   edge, is the integral of the child's local boundary sector plus its recursive
--   exact-depth child subtrees.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L890-L919
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L890-L919

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_mixedPartialList_cons_interpWithFill_eq_integral_child_standard_add_sum
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    (∫ t in 0..top,
        mixedPartialList (e.val :: pref.reverse) ρ
          (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)) =
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
