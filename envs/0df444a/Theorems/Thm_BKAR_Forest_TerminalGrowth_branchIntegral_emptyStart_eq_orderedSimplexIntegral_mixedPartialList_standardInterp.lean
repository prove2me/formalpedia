-- Prove2me | Theorems.Thm_BKAR_Forest_TerminalGrowth_branchIntegral_emptyStart_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
-- name    : BKAR.Forest.TerminalGrowth.branchIntegral_emptyStart_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:46:18.574377+00:00
-- url     : https://prove2.me/theorems/c1af217c-1c00-57d4-8ac5-b4c713e3ecda
-- title:
--   Terminal Growth: branch Integral empty Start eq ordered Simplex Integral mixed Partial List standard Interp
-- statement:
--   The Terminal Growth construction uses the branch Integral empty Start eq ordered Simplex Integral mixed Partial List standard Interp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L271-L278
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedTerminalGrowth.lean#L271-L278

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

theorem BKAR.Forest.TerminalGrowth.branchIntegral_emptyStart_eq_orderedSimplexIntegral_mixedPartialList_standardInterp
    (data : TerminalGrowth (Forest.empty V)) (ρ : (Edge V → ℝ) → ℝ) :
    data.branchIntegral emptyParam ρ =
      orderedSimplexIntegral data.order
        (fun ts => mixedPartialList data.order.reverse ρ
          (data.terminal.standardInterp (data.growth.params emptyParam ts))) := by sorry
