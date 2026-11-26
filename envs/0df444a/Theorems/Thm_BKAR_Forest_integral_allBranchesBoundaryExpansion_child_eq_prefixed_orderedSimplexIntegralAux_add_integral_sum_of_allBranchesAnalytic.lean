-- Prove2me | Theorems.Thm_BKAR_Forest_integral_allBranchesBoundaryExpansion_child_eq_prefixed_orderedSimplexIntegralAux_add_integral_sum_of_allBranchesAnalytic
-- name    : BKAR.Forest.integral_allBranchesBoundaryExpansion_child_eq_prefixed_orderedSimplexIntegralAux_add_integral_sum_of_allBranchesAnalytic
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:16:32.597115+00:00
-- url     : https://prove2.me/theorems/ad23b8f9-6690-5bcf-b27e-aeb0ed24a104
-- title:
--   Forest: integral all Branches Boundary Expansion child eq prefixed ordered Simplex Integral Aux add integral sum of all Branches Analytic
-- statement:
--   Nonterminal child split with the linearity hypotheses read from
--   `allBranchesAnalytic`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L686-L718
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/AllBranchesRegrouping.lean#L686-L718

import Definitions.Def_BKAR_OrderedAssembly_AllBranches
import Definitions.Def_BKAR_OrderedAssembly_AllBranchesRegrouping
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.integral_allBranchesBoundaryExpansion_child_eq_prefixed_orderedSimplexIntegralAux_add_integral_sum_of_allBranchesAnalytic
    (choices : ActiveExtensionChoice V)
    (F : Forest V) (e : {e // e ∈ F.activeEdges})
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hanalytic :
      allBranchesAnalytic choices F.activeEdges.card
        F pref prefixTs top ρ) :
    (∫ t in 0..top,
        allBranchesBoundaryExpansion choices
          (choices F e).forest.activeEdges.card
          (choices F e).forest (pref ++ [e.val])
          (prefixTs ++ [t]) t ρ) =
      orderedSimplexIntegralAux top [e.val]
        (fun ts => mixedPartialList (pref ++ [e.val]).reverse ρ
          ((choices F e).forest.standardInterp
            ((choices F e).forest.paramsOfOrder (pref ++ [e.val])
              (prefixTs ++ ts)))) +
        ∫ t in 0..top,
          Finset.sum (choices F e).forest.activeEdges.attach
            (fun e' => ∫ s in 0..t,
              allBranchesBoundaryExpansion choices
                (choices (choices F e).forest e').forest.activeEdges.card
                (choices (choices F e).forest e').forest
                ((pref ++ [e.val]) ++ [e'.val])
                ((prefixTs ++ [t]) ++ [s]) s ρ) := by sorry
