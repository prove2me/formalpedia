-- Prove2me | Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
-- name    : BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:28:51.410813+00:00
-- url     : https://prove2.me/theorems/1aa7508c-546e-592d-8e0a-957170be19f1
-- title:
--   Forest: mixed Partial List interp With Fill eq standard Interp of active Edges eq empty
-- statement:
--   Terminal ordered-derivative form: with no active edges left, the interpolation
--   parameter can be replaced by the standard configuration.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L312-L317
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L312-L317

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_of_activeEdges_eq_empty
    (F : Forest V) (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (t : ℝ) (hF : F.activeEdges = ∅) :
    mixedPartialList es ρ (F.interpWithFill u t) =
      mixedPartialList es ρ (F.standardInterp u) := by sorry
