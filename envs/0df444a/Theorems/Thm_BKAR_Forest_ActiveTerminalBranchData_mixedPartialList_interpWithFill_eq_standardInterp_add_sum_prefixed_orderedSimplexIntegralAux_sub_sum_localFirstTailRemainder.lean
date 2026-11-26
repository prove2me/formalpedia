-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_mixedPartialList_interpWithFill_eq_standardInterp_add_sum_prefixed_orderedSimplexIntegralAux_sub_sum_localFirstTailRemainder
-- name    : BKAR.Forest.ActiveTerminalBranchData.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_prefixed_orderedSimplexIntegralAux_sub_sum_localFirstTailRemainder
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:42:21.356661+00:00
-- url     : https://prove2.me/theorems/85dc882c-9a99-4366-a234-3c124150aacb
-- title:
--   Active Terminal Branch Data: mixed Partial List interp With Fill eq standard Interp add sum prefixed ordered Simplex Integral Aux sub sum local First Tail Remainder
-- statement:
--   Prefixed sector form of the local selected-terminal recursion.  This is the
--   shape needed by the finishing induction: selected terminal branches are already
--   expressed using the accumulated edge order `pref`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean#L121-L154
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedAssembly/LocalRecursion.lean#L121-L154

import Definitions.Def_BKAR_CubePartition_Prefixed
import Definitions.Def_BKAR_OrderedAssembly_LocalRecursion
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_prefixed_orderedSimplexIntegralAux_sub_sum_localFirstTailRemainder
    (data : ActiveTerminalBranchData F)
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam,
      t ≤ F.paramsOfOrder pref prefixTs e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList pref.reverse ρ)
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: pref.reverse) ρ
          (F.interpWithFill (F.paramsOfOrder pref prefixTs) t))
        MeasureTheory.volume 0 b) :
    mixedPartialList pref.reverse ρ
        (F.interpWithFill (F.paramsOfOrder pref prefixTs) b) =
      mixedPartialList pref.reverse ρ
        (F.standardInterp (F.paramsOfOrder pref prefixTs)) +
        Finset.sum F.activeEdges.attach
          (fun e => orderedSimplexIntegralAux b (data.growth e).order
            (fun ts =>
              mixedPartialList (pref ++ (data.growth e).order).reverse ρ
                ((data.growth e).terminal.standardInterp
                  ((data.growth e).terminal.paramsOfOrder
                    (pref ++ (data.growth e).order) (prefixTs ++ ts))))) -
          Finset.sum F.activeEdges.attach
            (fun e => data.localFirstTailRemainder e b
              (F.paramsOfOrder pref prefixTs) pref.reverse ρ) := by sorry
