-- Prove2me | Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges_of_activeEdges_eq_empty
-- name    : BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:34:58.749408+00:00
-- url     : https://prove2.me/theorems/ca608103-1ec7-4472-ad1f-10e76764a331
-- title:
--   Forest: mixed Partial List interp With Fill eq standard Interp add sum integrals active Edges of active Edges eq empty
-- statement:
--   Terminal form of the ordered-recursion step: with no active edges, the boundary
--   term is the whole contribution and the next remainder is zero.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L567-L580
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L567-L580

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges_of_activeEdges_eq_empty
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ) (hF : F.activeEdges = ∅) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        Finset.sum F.activeEdges
          (fun e => ∫ t in 0..b,
            mixedPartialList (e :: es) ρ (F.interpWithFill u t)) := by sorry
