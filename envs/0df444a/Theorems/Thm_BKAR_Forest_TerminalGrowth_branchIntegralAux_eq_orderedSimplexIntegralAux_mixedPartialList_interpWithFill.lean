-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
-- name    : BKAR.Forest.TerminalGrowth.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:43:39.489639+00:00
-- url     : https://prove2.me/theorems/36e7dfd0-f31c-4fb7-8ac9-ca15369c7c95
-- title:
--   Terminal Growth: branch Integral Aux eq ordered Simplex Integral Aux mixed Partial List interp With Fill
-- statement:
--   The same terminal branch integral, with the final standard interpolation
--   expressed as the terminal fill-parameter interpolation.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L284-L295
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L284-L295

import Definitions.Def_BKAR_OrderedRemainder
import Definitions.Def_BKAR_OrderedTerminalGrowth
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
noncomputable section
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.TerminalGrowth
variable {F : Forest V}

theorem BKAR.Forest.TerminalGrowth.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_interpWithFill
    (data : TerminalGrowth F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) :
    data.branchIntegralAux top u ρ =
      orderedSimplexIntegralAux top data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.interpWithFill (data.growth.params u ts) b)) := by sorry
