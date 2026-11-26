-- Prove2me | Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_integral_sum
-- name    : BKAR.Forest.integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_integral_sum
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:01:22.716802+00:00
-- url     : https://prove2.me/theorems/bbcd0319-2429-4148-ad1d-fd9b61197764
-- title:
--   Forest: integral all Branches Boundary Expansion child eq integral standard add integral sum
-- statement:
--   Linearity bridge for one nonterminal child of the exact-depth boundary tree.
--
--   The theorem is intentionally local: it separates the boundary subtree into the
--   child's first ordered sector and the recursive exact-depth grandchildren once
--   those two functions are known to be interval-integrable.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L588-L631
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L588-L631

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_allBranchesBoundaryExpansion_child_eq_integral_standard_add_integral_sum
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hstd :
      IntervalIntegrable
        (fun t : ℝ =>
          mixedPartialList (pref ++ [e.val]).reverse ρ
            ((choices F e).forest.standardInterp
              ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
                (prefixTs ++ [t]))))
        MeasureTheory.volume 0 top)
    (hrec :
      IntervalIntegrable
        (fun t : ℝ =>
          Finset.sum (choices F e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices (choices F e).forest e').forest.activeEdges.card
                (choices (choices F e).forest e').forest
                ((pref ++ [e.val]) ++ [e'.val])
                ((prefixTs ++ [t]) ++ [s]) s ρ))
        MeasureTheory.volume 0 top) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ) =
      (∫ t in 0..top,
        mixedPartialList (pref ++ [e.val]).reverse ρ
          ((choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
              (prefixTs ++ [t])))) +
        ∫ t in 0..top,
          Finset.sum (choices F e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices (choices F e).forest e').forest.activeEdges.card
                (choices (choices F e).forest e').forest
                ((pref ++ [e.val]) ++ [e'.val])
                ((prefixTs ++ [t]) ++ [s]) s ρ) := by sorry
