-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
-- name    : BKAR.Forest.ActiveBranchData.singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:36:45.782585+00:00
-- url     : https://prove2.me/theorems/ad3289a9-01b3-4d96-8998-ee82ece65c72
-- title:
--   Active Branch Data: singleton branch Integral Aux eq sum integrals mixed Partial List interp With Fill of active Edges eq empty
-- statement:
--   Accumulated-derivative version of the terminal singleton branch-sum identity.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L288-L307
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L288-L307

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_interpWithFill_of_activeEdges_eq_empty
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (es : List (Edge V)) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions).branchIntegralAux top u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..top,
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.interpWithFill
              ((extensions e).extension.extendParam u t) t)) := by sorry
