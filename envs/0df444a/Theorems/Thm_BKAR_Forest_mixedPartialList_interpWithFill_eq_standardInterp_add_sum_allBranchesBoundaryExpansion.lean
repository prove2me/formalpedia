-- Prove2me | Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_standardInterp_add_sum_allBranchesBoundaryExpansion
-- name    : BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_allBranchesBoundaryExpansion
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:44:10.314912+00:00
-- url     : https://prove2.me/theorems/08b11dbf-6b3f-52a9-9fb7-3fb1029daa92
-- title:
--   Forest: mixed Partial List interp With Fill eq standard Interp add sum all Branches Boundary Expansion
-- statement:
--   Arbitrary-node exact-depth recursion: the current fill-parameter remainder is
--   the local boundary sector plus exact-depth boundary subtrees below all active
--   children.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L740-L761
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L740-L761

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_allBranchesBoundaryExpansion
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) top) =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..top,
            allBranchesBoundaryExpansion choices
              (choices F e).forest.activeEdges.card
              (choices F e).forest (pref ++ [e.val])
              (prefixTs ++ [t]) t ρ) := by sorry
