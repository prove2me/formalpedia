-- Prove2me | Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_allBranchesBoundaryExpansion_activeEdges_card
-- name    : BKAR.Forest.mixedPartialList_interpWithFill_eq_allBranchesBoundaryExpansion_activeEdges_card
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:58:27.631789+00:00
-- url     : https://prove2.me/theorems/2979695f-1ee1-5019-93cb-e17754afdef7
-- title:
--   Forest: mixed Partial List interp With Fill eq all Branches Boundary Expansion active Edges card
-- statement:
--   Exact-depth boundary expansion equals the current fill-parameter remainder
--   under the corresponding all-branches analytic hypotheses.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L559-L577
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L559-L577

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mixedPartialList_interpWithFill_eq_allBranchesBoundaryExpansion_activeEdges_card
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
      allBranchesBoundaryExpansion choices F.activeEdges.card
        F pref prefixTs top ρ := by sorry
