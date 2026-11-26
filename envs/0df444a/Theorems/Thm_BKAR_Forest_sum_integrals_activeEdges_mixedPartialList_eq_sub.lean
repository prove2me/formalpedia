-- Prove2me | Theorems.Thm_BKAR_Forest_sum_integrals_activeEdges_mixedPartialList_eq_sub
-- name    : BKAR.Forest.sum_integrals_activeEdges_mixedPartialList_eq_sub
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:34:45.954833+00:00
-- url     : https://prove2.me/theorems/bfe1012c-133e-4c25-9a58-efd4e4583af1
-- title:
--   Forest: sum integrals active Edges mixed Partial List eq sub
-- statement:
--   Ordered-mixed-partial version of the integrated differential identity. This is the
--   form used when the ordered recursion has already accumulated the derivative
--   list `es` and expands by one active edge.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L506-L524
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L506-L524

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.sum_integrals_activeEdges_mixedPartialList_eq_sub (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hρ : ∀ t ∈ Set.uIcc a b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume a b) :
    Finset.sum F.activeEdges
      (fun e => ∫ t in a..b,
        mixedPartialList (e :: es) ρ (F.interpWithFill u t)) =
      mixedPartialList es ρ (F.interpWithFill u b) -
        mixedPartialList es ρ (F.interpWithFill u a) := by sorry
