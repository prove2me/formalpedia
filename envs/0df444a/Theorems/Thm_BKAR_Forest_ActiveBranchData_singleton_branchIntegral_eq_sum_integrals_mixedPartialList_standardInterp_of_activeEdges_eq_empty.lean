-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_singleton_branchIntegral_eq_sum_integrals_mixedPartialList_standardInterp_of_activeEdges_eq_empty
-- name    : BKAR.Forest.ActiveBranchData.singleton_branchIntegral_eq_sum_integrals_mixedPartialList_standardInterp_of_activeEdges_eq_empty
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:21:59.106305+00:00
-- url     : https://prove2.me/theorems/ec99d380-93dd-4e4e-ba17-93ad67f5adfa
-- title:
--   Active Branch Data: singleton branch Integral eq sum integrals mixed Partial List standard Interp of active Edges eq empty
-- statement:
--   Unit-simplex version of
--   `ActiveBranchData.singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp_of_activeEdges_eq_empty`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L364-L378
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L364-L378

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.singleton_branchIntegral_eq_sum_integrals_mixedPartialList_standardInterp_of_activeEdges_eq_empty
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val)
    (es : List (Edge V))
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ)
    (hterm : ∀ e : {e // e ∈ F.activeEdges},
      (extensions e).forest.activeEdges = ∅) :
    (singleton extensions).branchIntegral u (mixedPartialList es ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => ∫ t in 0..(1 : ℝ),
          mixedPartialList (e.val :: es) ρ
            ((extensions e).forest.standardInterp
              ((extensions e).extension.extendParam u t))) := by sorry
