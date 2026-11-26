-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_intervalIntegrable_partialDeriv_interpWithFill_extension
-- name    : BKAR.Forest.EdgeExtension.intervalIntegrable_partialDeriv_interpWithFill_extension
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:27:44.594543+00:00
-- url     : https://prove2.me/theorems/c824ecb8-ceec-41d0-bce5-da24f307b961
-- title:
--   Edge Extension: interval Integrable partial Deriv interp With Fill extension
-- statement:
--   Interval integrability transfers across the one-edge extension
--   re-interpretation.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L79-L93
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L79-L93

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

theorem BKAR.Forest.EdgeExtension.intervalIntegrable_partialDeriv_interpWithFill_extension
    (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (ρ : (Edge V → ℝ) → ℝ) (a b : ℝ)
    (hbound : ∀ t ∈ Set.uIcc a b, ∀ e : F.EdgeParam, t ≤ u e)
    (hint : IntervalIntegrable
      (fun t : ℝ => partialDeriv e₀ ρ (F.interpWithFill u t))
      MeasureTheory.volume a b) :
    IntervalIntegrable
      (fun t : ℝ => partialDeriv e₀ ρ
        (F'.interpWithFill (h.extendParam u t) t))
      MeasureTheory.volume a b := by sorry
