-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesAnalytic_child_standard_intervalIntegrable
-- name    : BKAR.Forest.allBranchesAnalytic.child_standard_intervalIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:59:50.309076+00:00
-- url     : https://prove2.me/theorems/43cdac9d-d1e7-538a-8f61-d992347c392b
-- title:
--   all Branches Analytic: child standard interval Integrable
-- statement:
--   The child first-sector integrability contained in `allBranchesAnalytic`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L532-L552
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L532-L552

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesAnalytic.child_standard_intervalIntegrable
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    IntervalIntegrable
      (fun t : ℝ => mixedPartialList (pref ++ [e.val]).reverse ρ
        ((choices F e).forest.standardInterp
          ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
            (prefixTs ++ [t]))))
      MeasureTheory.volume 0 top := by sorry
