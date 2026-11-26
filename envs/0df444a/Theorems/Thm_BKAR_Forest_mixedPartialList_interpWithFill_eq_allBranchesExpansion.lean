-- Prove2me | Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_allBranchesExpansion
-- name    : BKAR.Forest.mixedPartialList_interpWithFill_eq_allBranchesExpansion
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:58:18.624882+00:00
-- url     : https://prove2.me/theorems/3dbabd03-6773-59fb-93e3-3f6aa65cda81
-- title:
--   Forest: mixed Partial List interp With Fill eq all Branches Expansion
-- statement:
--   The all-branches induction invariant: expanding every active edge for `n`
--   layers preserves the current fill-parameter remainder.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L202-L280
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranches.lean#L202-L280

import Definitions.Def_BKAR_CubePartition_Support
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mixedPartialList_interpWithFill_eq_allBranchesExpansion
    (choices : ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ) (ρ : (Edge V → ℝ) → ℝ),
      pref.toFinset = F.edges →
      prefixTs.length = pref.length →
      allBranchesAnalytic choices n F pref prefixTs top ρ →
      mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) top) =
        allBranchesExpansion choices n F pref prefixTs top ρ
  := by sorry
