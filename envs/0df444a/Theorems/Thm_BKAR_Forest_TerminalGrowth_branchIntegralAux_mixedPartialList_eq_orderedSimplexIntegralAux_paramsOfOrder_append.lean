-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegralAux_mixedPartialList_eq_orderedSimplexIntegralAux_paramsOfOrder_append
-- name    : BKAR.Forest.TerminalGrowth.branchIntegralAux_mixedPartialList_eq_orderedSimplexIntegralAux_paramsOfOrder_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:48:44.21717+00:00
-- url     : https://prove2.me/theorems/69723a20-7342-550a-a2a7-140fb82fd421
-- title:
--   Terminal Growth: branch Integral Aux mixed Partial List eq ordered Simplex Integral Aux params Of Order append
-- statement:
--   A terminal tail integral at a nonempty recursion node can be read as the
--   ordered simplex for the accumulated prefix followed by the tail order.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L134-L151
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Branches.lean#L134-L151

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_CubePartition_Branches
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.branchIntegralAux_mixedPartialList_eq_orderedSimplexIntegralAux_paramsOfOrder_append
    (data : TerminalGrowth F) (pref : List (Edge V)) (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length)
    (top : ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top (F.paramsOfOrder pref prefixTs)
        (mixedPartialList pref.reverse ρ) =
      orderedSimplexIntegralAux top data.order
        (fun ts => mixedPartialList (pref ++ data.order).reverse ρ
          (data.terminal.standardInterp
            (data.terminal.paramsOfOrder (pref ++ data.order)
              (prefixTs ++ ts)))) := by sorry
