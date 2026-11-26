-- Prove2me | Theorems.Thm_BKAR_Forest_ActiveTerminalBranchData_branchIntegralAux_mixedPartialList_eq_sum_prefixed_orderedSimplexIntegralAux
-- name    : BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_mixedPartialList_eq_sum_prefixed_orderedSimplexIntegralAux
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:02:06.097862+00:00
-- url     : https://prove2.me/theorems/37737fc5-025e-5372-ab28-2bec6009d5d9
-- title:
--   Active Terminal Branch Data: branch Integral Aux mixed Partial List eq sum prefixed ordered Simplex Integral Aux
-- statement:
--   At a general recursion node, the selected terminal branch sum is a finite sum
--   of ordered simplices whose edge order is the accumulated prefix followed by
--   the selected terminal growth order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Prefixed.lean#L29-L47
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Prefixed.lean#L29-L47

import Definitions.Def_BKAR_CubePartition_Branches
import Definitions.Def_BKAR_CubePartition_Prefixed
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.ActiveTerminalBranchData
variable {F : Forest V}

theorem BKAR.Forest.ActiveTerminalBranchData.branchIntegralAux_mixedPartialList_eq_sum_prefixed_orderedSimplexIntegralAux
    (data : ActiveTerminalBranchData F)
    (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top (F.paramsOfOrder pref prefixTs)
        (mixedPartialList pref.reverse ρ) =
      Finset.sum F.activeEdges.attach
        (fun e => orderedSimplexIntegralAux top (data.growth e).order
          (fun ts => mixedPartialList (pref ++ (data.growth e).order).reverse ρ
            ((data.growth e).terminal.standardInterp
              ((data.growth e).terminal.paramsOfOrder
                (pref ++ (data.growth e).order) (prefixTs ++ ts))))) := by sorry
