-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp
-- name    : BKAR.Forest.TerminalGrowth.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:43:45.179098+00:00
-- url     : https://prove2.me/theorems/2ceb8483-9e9b-41f6-9d43-223259560776
-- title:
--   Terminal Growth: branch Integral Aux eq ordered Simplex Integral Aux mixed Partial List standard Interp
-- statement:
--   A terminal branch integral in the standard interpolation form used by BKAR
--   main terms.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L246-L255
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L246-L255

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

theorem BKAR.Forest.TerminalGrowth.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp
    (data : TerminalGrowth F) (top : ℝ)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegralAux top u ρ =
      orderedSimplexIntegralAux top data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.standardInterp (data.growth.params u ts))) := by sorry
