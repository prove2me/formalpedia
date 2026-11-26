-- Prove2me | Theorems.Thm_BKAR_Forest_sum_integrals_activeEdges_mixedPartialList_eq_zero_of_activeEdges_eq_empty
-- name    : BKAR.Forest.sum_integrals_activeEdges_mixedPartialList_eq_zero_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:33.604612+00:00
-- url     : https://prove2.me/theorems/8ae4399c-b7e5-4eb5-a94b-7b117ca24eb7
-- title:
--   Forest: sum integrals active Edges mixed Partial List eq zero of active Edges eq empty
-- statement:
--   The ordered active-edge integral remainder is zero when no active edges remain.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L527-L534
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L527-L534

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_integrals_activeEdges_mixedPartialList_eq_zero_of_activeEdges_eq_empty
    (F : Forest V) (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ) (hF : F.activeEdges = ∅) :
    Finset.sum F.activeEdges
      (fun e => ∫ t in a..b,
        mixedPartialList (e :: es) ρ (F.interpWithFill u t)) = 0 := by sorry
