-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_allBranchesAnalytic_smooth_obligations
-- name    : BKAR.BKARContDiff.allBranchesAnalytic_smooth_obligations
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:20:20.609091+00:00
-- url     : https://prove2.me/theorems/62951723-34a6-5ac7-93df-a12b31a9cae1
-- title:
--   BKARCont Diff: all Branches Analytic smooth obligations
-- statement:
--   The non-recursive smoothness/integrability side conditions in
--   `allBranchesAnalytic` follow from global `C^∞` smoothness of `ρ`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L57-L92
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L57-L92

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.allBranchesAnalytic_smooth_obligations
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length) :
    (∀ t ∈ Set.uIcc 0 top,
      DifferentiableAt ℝ (BKAR.mixedPartialList pref.reverse ρ)
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t)) ∧
    (∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ =>
          BKAR.mixedPartialList (e :: pref.reverse) ρ
            (F.interpWithFill (F.paramsOfOrder pref prefixTs) t))
        MeasureTheory.volume 0 top) ∧
    (∀ e : {e // e ∈ F.activeEdges},
      IntervalIntegrable
        (fun t : ℝ =>
          BKAR.mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ [t]))))
        MeasureTheory.volume 0 top) := by sorry
