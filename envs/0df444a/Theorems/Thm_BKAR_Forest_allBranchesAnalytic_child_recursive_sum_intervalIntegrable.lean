-- Prove2me | Theorems.Thm_BKAR_Forest_allBranchesAnalytic_child_recursive_sum_intervalIntegrable
-- name    : BKAR.Forest.allBranchesAnalytic.child_recursive_sum_intervalIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:00:13.447461+00:00
-- url     : https://prove2.me/theorems/78d03f80-bd72-44d5-82ff-8a9ad7f32705
-- title:
--   all Branches Analytic: child recursive sum interval Integrable
-- statement:
--   The recursive child-sum integrability contained in `allBranchesAnalytic`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L555-L579
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L555-L579

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.allBranchesAnalytic.child_recursive_sum_intervalIntegrable
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    IntervalIntegrable
      (fun t : ℝ =>
        Finset.sum (choices F e).forest.activeEdges.attach
          (fun e' => ∫ s in 0..t,
            allBranchesBoundaryExpansion choices
              (choices (choices F e).forest e').forest.activeEdges.card
              (choices (choices F e).forest e').forest
              ((pref ++ [e.val]) ++ [e'.val])
              ((prefixTs ++ [t]) ++ [s]) s ρ))
      MeasureTheory.volume 0 top := by sorry
