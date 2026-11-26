-- Prove2me | Theorems.Thm_BKAR_Forest_mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions
-- name    : BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:35:12.637024+00:00
-- url     : https://prove2.me/theorems/15b2836f-7e2f-54eb-b11d-7486057e4e13
-- title:
--   Forest: mixed Partial List interp With Fill eq standard Interp add sum active Extensions
-- statement:
--   Boundary-expansion form whose active-edge remainder has already been
--   reinterpreted as a sum over explicitly chosen one-edge forest extensions.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L614-L638
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L614-L638

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.mixedPartialList_interpWithFill_eq_standardInterp_add_sum_activeExtensions
    (F : Forest V)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc 0 b, ∀ e : F.EdgeParam, t ≤ u e)
    (hρ : ∀ t ∈ Set.uIcc 0 b,
      DifferentiableAt ℝ (mixedPartialList es ρ) (F.interpWithFill u t))
    (hint : ∀ e ∈ F.activeEdges,
      IntervalIntegrable
        (fun t : ℝ => mixedPartialList (e :: es) ρ
          (F.interpWithFill u t))
        MeasureTheory.volume 0 b)
    (extensions : ∀ e : {e // e ∈ F.activeEdges},
      ActiveExtension F e.val) :
    mixedPartialList es ρ (F.interpWithFill u b) =
      mixedPartialList es ρ (F.standardInterp u) +
        Finset.sum F.activeEdges.attach
          (fun e => ∫ t in 0..b,
            mixedPartialList (e.val :: es) ρ
              ((extensions e).forest.interpWithFill
                ((extensions e).extension.extendParam u t) t)) := by sorry
