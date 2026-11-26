-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_allBranchesAnalytic_of_contDiff
-- name    : BKAR.BKARContDiff.allBranchesAnalytic_of_contDiff
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:20:36.270793+00:00
-- url     : https://prove2.me/theorems/8ec51b85-b658-5718-93f2-e1a38b5149e2
-- title:
--   BKARCont Diff: all Branches Analytic of cont Diff
-- statement:
--   Global recursive discharge of the `allBranchesAnalytic` predicate from
--   `C^∞` smoothness of `ρ` and the ordered-parameter bound carried by the
--   recursion node.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L328-L370
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L328-L370

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.allBranchesAnalytic_of_contDiff
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V) :
    ∀ (n : Nat) (F : Forest V) (pref : List (Edge V))
      (prefixTs : List ℝ) (top : ℝ),
      pref.toFinset = F.edges →
      prefixTs.length = pref.length →
      0 ≤ top →
      (∀ t ∈ Set.uIcc 0 top, ∀ e : F.EdgeParam,
        t ≤ F.paramsOfOrder pref prefixTs e) →
      Forest.allBranchesAnalytic choices n F pref prefixTs top ρ
  := by sorry
