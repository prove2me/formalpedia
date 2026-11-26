-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_mixedPartialList_interpWithFill_eq_standardInterp_add_branchIntegralAux_sub_sum_localFirstTailRemainder
-- name    : BKAR.Forest.ActiveTerminalBranchData.mixedPartialList_interpWithFill_eq_standardInterp_add_branchIntegralAux_sub_sum_localFirstTailRemainder
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:39.28508+00:00
-- url     : https://prove2.me/theorems/12b2a39e-3f2c-4754-8e42-8babd3152762
-- title:
--   Active Terminal Branch Data: mixed Partial List interp With Fill eq standard Interp add branch Integral Aux sub sum local First Tail Remainder
-- statement:
--   Local selected-terminal recursion.  Starting from any forest and accumulated
--   derivative list, one FTC layer contributes the selected terminal branch sum
--   and leaves exactly the local first-tail errors.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean#L91-L114
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean#L91-L114

import Definitions.Def_BKAR_CubePartition_Prefixed
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.mixedPartialList_interpWithFill_eq_standardInterp_add_branchIntegralAux_sub_sum_localFirstTailRemainder
    (data : ActiveTerminalBranchData F)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam, t ≤ u e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume 0 b) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        data.branchIntegralAux b u (mixedPartialList es ρ) -
          Finset.sum F.activeEdges.attach
            (fun e => data.localFirstTailRemainder e b u es ρ) := by sorry
