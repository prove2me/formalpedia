-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_mixedPartialList_cons_interpWithFill_eq_extension
-- name    : BKAR.Forest.EdgeExtension.mixedPartialList_cons_interpWithFill_eq_extension
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:31:06.458965+00:00
-- url     : https://prove2.me/theorems/94594dea-4bcd-5def-b5d7-99c72252d9fd
-- title:
--   Edge Extension: mixed Partial List cons interp With Fill eq extension
-- statement:
--   Ordered-derivative form of the one-edge extension re-interpretation. The new
--   edge is consed onto the explicit derivative list.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L114-L124
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedExpansion.lean#L114-L124

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

theorem BKAR.Forest.EdgeExtension.mixedPartialList_cons_interpWithFill_eq_extension
    (h : EdgeExtension F F' e₀)
    (es : List (Edge V)) (u : F.EdgeParam → ℝ)
    (ρ : (Edge V → ℝ) → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) :
    partialDeriv e₀ (mixedPartialList es ρ) (F.interpWithFill u s) =
      mixedPartialList (e₀ :: es) ρ
        (F'.interpWithFill (h.extendParam u s) s) := by sorry
