-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesExpansion_zero
-- name    : BKAR.Forest.allBranchesExpansion_zero
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:57:12.051245+00:00
-- url     : https://prove2.me/theorems/310232a3-d1f7-5266-aac1-ad500b7079f6
-- title:
--   Forest: all Branches Expansion zero
-- statement:
--   The Forest construction uses the all Branches Expansion zero property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L62-L69
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L62-L69

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesExpansion_zero
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    allBranchesExpansion choices 0 F pref prefixTs top ρ =
      mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) top) := by sorry
