-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_paramValue_extend_new
-- name    : BKAR.Forest.EdgeExtension.paramValue_extend_new
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:18.762623+00:00
-- url     : https://prove2.me/theorems/d318ef9b-b11d-4c96-8b57-08cb32d444a6
-- title:
--   Edge Extension: param Value extend new
-- statement:
--   The Edge Extension construction uses the param Value extend new property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L384-L388
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L384-L388

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

theorem BKAR.Forest.EdgeExtension.paramValue_extend_new (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (s : ℝ) :
    F'.paramValue (h.extendParam u s) e₀ = s := by sorry
