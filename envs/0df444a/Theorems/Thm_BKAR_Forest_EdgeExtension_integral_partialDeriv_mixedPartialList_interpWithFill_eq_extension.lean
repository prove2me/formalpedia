-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_integral_partialDeriv_mixedPartialList_interpWithFill_eq_extension
-- name    : BKAR.Forest.EdgeExtension.integral_partialDeriv_mixedPartialList_interpWithFill_eq_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:27.806835+00:00
-- url     : https://prove2.me/theorems/7710a8ba-b633-432f-9d99-dabd7263d2c1
-- title:
--   Edge Extension: integral partial Deriv mixed Partial List interp With Fill eq extension
-- statement:
--   Integral congruence for the ordered-derivative form of the one-edge extension
--   re-interpretation.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L151-L162
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L151-L162

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_BKAR_ForestGraph
import Definitions.Def_BKAR_Differential
import Definitions.Def_BKAR_OrderedExpansion
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}

theorem BKAR.Forest.EdgeExtension.integral_partialDeriv_mixedPartialList_interpWithFill_eq_extension
    (h : EdgeExtension F F' e₀)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e) :
    (∫ t in a..b,
        partialDeriv e₀ (mixedPartialList es ρ) (F.interpWithFill u t)) =
      ∫ t in a..b, mixedPartialList (e₀ :: es) ρ
        (F'.interpWithFill (h.extendParam u t) t) := by sorry
