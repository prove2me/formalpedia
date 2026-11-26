-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_partialDeriv_interpWithFill_eq_extension
-- name    : BKAR.Forest.EdgeExtension.partialDeriv_interpWithFill_eq_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:00.178363+00:00
-- url     : https://prove2.me/theorems/05d90402-b662-4244-b9b8-ff8ccad759bb
-- title:
--   Edge Extension: partial Deriv interp With Fill eq extension
-- statement:
--   Pointwise re-interpretation of an active-edge integrand on a one-edge
--   extension, under the ordered-simplex bound on the old parameters.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L67-L73
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L67-L73

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

theorem BKAR.Forest.EdgeExtension.partialDeriv_interpWithFill_eq_extension (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) :
    partialDeriv e₀ ρ (F.interpWithFill u s) =
      partialDeriv e₀ ρ
        (F'.interpWithFill (h.extendParam u s) s) := by sorry
