-- Prove2me | Theorems.Thm_BKAR_Forest_mixedPartial_eq_mixedPartialList_of_mem_edgeOrders
-- name    : BKAR.Forest.mixedPartial_eq_mixedPartialList_of_mem_edgeOrders
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:04:17.864809+00:00
-- url     : https://prove2.me/theorems/39780211-fdad-5bc7-b84e-63518d2c6902
-- title:
--   Forest: mixed Partial eq mixed Partial List of mem edge Orders
-- statement:
--   The Forest construction uses the mixed Partial eq mixed Partial List of mem edge Orders property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDerivSymmetry.lean#L160-L167
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDerivSymmetry.lean#L160-L167

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Definitions.Def_BKAR_CubePartition_Orders
import Definitions.Def_BKAR_Smoothness
import Definitions.Def_BKAR_PartialDerivSymmetry
import Theorems.Thm_BKAR_EdgePath_IsSimplePath_reverse

set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest
variable (F : Forest V)
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.Forest.mixedPartial_eq_mixedPartialList_of_mem_edgeOrders
    {order : List (Edge V)} (horder : order ∈ F.edgeOrders)
    (hρ : BKARContDiff ρ) :
    F.mixedPartial ρ = BKAR.mixedPartialList order.reverse ρ := by sorry
