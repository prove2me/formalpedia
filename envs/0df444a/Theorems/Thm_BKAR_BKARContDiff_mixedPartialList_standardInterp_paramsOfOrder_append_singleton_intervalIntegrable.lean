-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_standardInterp_paramsOfOrder_append_singleton_intervalIntegrable
-- name    : BKAR.BKARContDiff.mixedPartialList_standardInterp_paramsOfOrder_append_singleton_intervalIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:13:15.634728+00:00
-- url     : https://prove2.me/theorems/c7a54973-f48c-4a68-a28d-0c33e44d9e25
-- title:
--   BKARCont Diff: mixed Partial List standard Interp params Of Order append singleton interval Integrable
-- statement:
--   The BKARCont Diff construction uses the mixed Partial List standard Interp params Of Order append singleton interval Integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Smoothness.lean#L60-L75
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/CubePartition/Smoothness.lean#L60-L75

import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_CubePartition_Smoothness
set_option autoImplicit false
open BKAR
open BKAR.BKARContDiff
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {ρ : (Edge V → ℝ) → ℝ}
variable {F F' : Forest V} {e : Edge V}

theorem BKAR.BKARContDiff.mixedPartialList_standardInterp_paramsOfOrder_append_singleton_intervalIntegrable
    (hρ : BKARContDiff ρ) (es : List (Edge V))
    (h : Forest.EdgeExtension F F' e) (pref : List (Edge V))
    (prefixTs : List ℝ)
    (hpref : pref.toFinset = F.edges)
    (hprefixTs : prefixTs.length = pref.length) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ =>
        BKAR.mixedPartialList es ρ
          (F'.standardInterp
            (F'.paramsOfOrder (pref ++ [e]) (prefixTs ++ [t]))))
      MeasureTheory.volume a b := by sorry
