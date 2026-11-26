-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveBranchData_singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp_of_activeEdges_eq_empty
-- name    : BKAR.Forest.ActiveBranchData.singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:36:25.399287+00:00
-- url     : https://prove2.me/theorems/8d347537-90f5-5b31-82e9-7b4e97188c6b
-- title:
--   Active Branch Data: singleton branch Integral Aux eq sum integrals mixed Partial List standard Interp of active Edges eq empty
-- statement:
--   Terminal singleton branches in the standard terminal-interpolation form.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L312-L338
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedRemainder.lean#L312-L338

import Definitions.Def_BKAR_OrderedRecursion
import Definitions.Def_BKAR_OrderedRemainder
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveBranchData.singleton_branchIntegralAux_eq_sum_integrals_mixedPartialList_standardInterp_of_activeEdges_eq_empty
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
            ((extensions e).forest.standardInterp
              ((extensions e).extension.extendParam u t))) := by sorry
