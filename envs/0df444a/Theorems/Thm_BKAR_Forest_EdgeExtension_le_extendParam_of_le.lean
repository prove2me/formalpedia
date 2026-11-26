-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_le_extendParam_of_le
-- name    : BKAR.Forest.EdgeExtension.le_extendParam_of_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:30:15.500413+00:00
-- url     : https://prove2.me/theorems/9a97ec77-2aec-5dc3-b75e-1a1f9be7edb9
-- title:
--   Edge Extension: le extend Param of le
-- statement:
--   The Edge Extension construction uses the le extend Param of le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L34-L39
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/OrderedParams.lean#L34-L39

import Definitions.Def_BKAR_OrderedSimplex
import Definitions.Def_BKAR_OrderedParams
set_option autoImplicit false
open BKAR
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e : Edge V}

theorem BKAR.Forest.EdgeExtension.le_extendParam_of_le (h : EdgeExtension F F' e)
    (u : F.EdgeParam → ℝ) {s top : ℝ}
    (hst : s ≤ top) (hu : ∀ e : F.EdgeParam, top ≤ u e)
    (e' : F'.EdgeParam) :
    s ≤ h.extendParam u s e' := by sorry
