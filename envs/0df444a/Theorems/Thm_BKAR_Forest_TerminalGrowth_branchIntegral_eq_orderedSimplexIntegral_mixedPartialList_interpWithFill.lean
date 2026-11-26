-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_interpWithFill
-- name    : BKAR.Forest.TerminalGrowth.branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_interpWithFill
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:23:52.250373+00:00
-- url     : https://prove2.me/theorems/80c88013-7716-4b54-9ac4-ac101265c3fa
-- title:
--   Terminal Growth: branch Integral eq ordered Simplex Integral mixed Partial List interp With Fill
-- statement:
--   Unit-simplex version of
--   `TerminalGrowth.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_interpWithFill`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L301-L309
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L301-L309

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

theorem BKAR.Forest.TerminalGrowth.branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_interpWithFill
    (data : TerminalGrowth F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) :
    data.branchIntegral u ρ =
      orderedSimplexIntegral data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.interpWithFill (data.growth.params u ts) b)) := by sorry
