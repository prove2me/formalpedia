-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_allBranchesAnalytic_child_recursive_sum_intervalIntegrable
-- name    : BKAR.BKARContDiff.allBranchesAnalytic_child_recursive_sum_intervalIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:20:43.115538+00:00
-- url     : https://prove2.me/theorems/b26297db-ea2f-47ca-b5ec-48c5e57f14aa
-- title:
--   BKARCont Diff: all Branches Analytic child recursive sum interval Integrable
-- statement:
--   The recursive child-sum integrability clause in `allBranchesAnalytic` follows
--   from global smoothness of `ρ`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L252-L321
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L252-L321

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.allBranchesAnalytic_child_recursive_sum_intervalIntegrable
    (hρ : BKARContDiff ρ) (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ) (top : ℝ)
    (hprefixTs : prefixTs.length = pref.length) :
    IntervalIntegrable
      (fun t : ℝ =>
        Finset.sum (choices F e).forest.activeEdges.attach
          (fun e' => ∫ s in 0..t,
            Forest.allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ))
      MeasureTheory.volume 0 top := by sorry
