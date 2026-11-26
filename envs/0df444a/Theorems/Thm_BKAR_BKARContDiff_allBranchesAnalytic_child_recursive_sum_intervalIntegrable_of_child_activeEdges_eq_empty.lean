-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_allBranchesAnalytic_child_recursive_sum_intervalIntegrable_of_child_activeEdges_eq_empty
-- name    : BKAR.BKARContDiff.allBranchesAnalytic_child_recursive_sum_intervalIntegrable_of_child_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T10:06:49.066524+00:00
-- url     : https://prove2.me/theorems/5c9b4330-0c06-5ae3-9c69-34c58dc06a91
-- title:
--   BKARCont Diff: all Branches Analytic child recursive sum interval Integrable of child active Edges eq empty
-- statement:
--   The recursive child-sum integrability clause is automatic when the selected
--   child is already terminal.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L139-L160
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesSmoothness.lean#L139-L160

import Definitions.Def_BKAR_OrderedAssembly_AllBranchesFiberSmoothness
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesSmoothness
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.allBranchesAnalytic_child_recursive_sum_intervalIntegrable_of_child_activeEdges_eq_empty
    (choices : Forest.ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hchild :
      (choices F e).forest.activeEdges = ∅) :
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
