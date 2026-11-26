-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_integral_partialDeriv_interpWithFill_eq_extension
-- name    : BKAR.Forest.EdgeExtension.integral_partialDeriv_interpWithFill_eq_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:24.865535+00:00
-- url     : https://prove2.me/theorems/1985c5b7-b200-497f-9fd1-83928260afbc
-- title:
--   Edge Extension: integral partial Deriv interp With Fill eq extension
-- statement:
--   The one-edge summand in the differential identity may be integrated after
--   reinterpreting its configuration on the extended forest.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L99-L108
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L99-L108

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

theorem BKAR.Forest.EdgeExtension.integral_partialDeriv_interpWithFill_eq_extension
    (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e) :
    (∫ t in a..b, partialDeriv e₀ ρ (F.interpWithFill u t)) =
      ∫ t in a..b, partialDeriv e₀ ρ
        (F'.interpWithFill (h.extendParam u t) t) := by sorry
