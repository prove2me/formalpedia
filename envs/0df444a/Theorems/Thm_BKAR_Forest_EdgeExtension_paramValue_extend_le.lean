-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_paramValue_extend_le
-- name    : BKAR.Forest.EdgeExtension.paramValue_extend_le
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:26.475689+00:00
-- url     : https://prove2.me/theorems/d6ec7874-5b06-4fba-85e8-bd0a904c541a
-- title:
--   Edge Extension: param Value extend le
-- statement:
--   The Edge Extension construction uses the param Value extend le property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L405-L411
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L405-L411

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}

theorem BKAR.Forest.EdgeExtension.paramValue_extend_le (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) {e : Edge V}
    (he : e ∈ F'.edges) :
    s ≤ F'.paramValue (h.extendParam u s) e := by sorry
