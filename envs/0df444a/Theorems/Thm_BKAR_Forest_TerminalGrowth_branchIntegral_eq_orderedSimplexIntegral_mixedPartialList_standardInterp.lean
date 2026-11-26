-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
-- name    : BKAR.Forest.TerminalGrowth.branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:43:39.220802+00:00
-- url     : https://prove2.me/theorems/44084106-882f-42e7-8bc6-ae8d40209c47
-- title:
--   Terminal Growth: branch Integral eq ordered Simplex Integral mixed Partial List standard Interp
-- statement:
--   Unit-simplex version of
--   `TerminalGrowth.branchIntegralAux_eq_orderedSimplexIntegralAux_mixedPartialList_standardInterp`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L261-L269
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L261-L269

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

theorem BKAR.Forest.TerminalGrowth.branchIntegral_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
    (data : TerminalGrowth F)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral u ρ =
      orderedSimplexIntegral data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.standardInterp (data.growth.params u ts))) := by sorry
