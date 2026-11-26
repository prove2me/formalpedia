-- Prove2me | Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
-- name    : BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:29:25.143157+00:00
-- url     : https://prove2.me/theorems/fb758127-5bfa-4d3b-831e-751bd9a38a4b
-- title:
--   Forest: mixed Partial List interp With Fill eq standard Interp add sum integrals active Edges
-- statement:
--   Boundary-expansion form of the ordered-mixed-partial differential identity. This is
--   the local recursion formula before the active-edge summands are reinterpreted
--   as one-edge forest extensions.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L541-L561
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L541-L561

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_integrals_activeEdges
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume 0 b) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        Finset.sum F.activeEdges
          (fun e => ∫ t in 0..b,
            mixedPartialList (e :: es) ρ (F.interpWithFill u t)) := by sorry
