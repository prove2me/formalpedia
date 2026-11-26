-- Prove2me | Theorems.Thm_BKAR_Forest_mixedPartialList_cons_interpWithFill_eq_allBranchesBoundaryExpansion_child
-- name    : BKAR.Forest.mixedPartialList_cons_interpWithFill_eq_allBranchesBoundaryExpansion_child
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:58:50.499355+00:00
-- url     : https://prove2.me/theorems/dc103178-ef38-50f4-898b-d7e21aa3b8fc
-- title:
--   Forest: mixed Partial List cons interp With Fill eq all Branches Boundary Expansion child
-- statement:
--   An active-edge summand in the parent fill-parameter remainder is exactly the
--   exact-depth boundary subtree below that active child.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L583-L669
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L583-L669

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mixedPartialList_cons_interpWithFill_eq_allBranchesBoundaryExpansion_child
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ)
    {t : ℝ} (ht : t ∈ Set.uIcc 0 top) :
    mixedPartialList (e.val :: pref.reverse) ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t) =
      allBranchesBoundaryExpansion choices
        (choices F e).forest.activeEdges.card
        (choices F e).forest (pref ++ [e.val])
        (prefixTs ++ [t]) t ρ := by sorry
