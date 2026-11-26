-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_paramValue_extend_old
-- name    : BKAR.Forest.EdgeExtension.paramValue_extend_old
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:13.9478+00:00
-- url     : https://prove2.me/theorems/24ec9d9f-f521-5a63-a89a-ade42005ca99
-- title:
--   Edge Extension: param Value extend old
-- statement:
--   The Edge Extension construction uses the param Value extend old property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L390-L394
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L390-L394

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

theorem BKAR.Forest.EdgeExtension.paramValue_extend_old (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (s : ℝ) {e : Edge V} (he : e ∈ F.edges) :
    F'.paramValue (h.extendParam u s) e = F.paramValue u e := by sorry
