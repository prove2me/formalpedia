-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_le_extendParam
-- name    : BKAR.Forest.EdgeExtension.le_extendParam
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:17:17.485488+00:00
-- url     : https://prove2.me/theorems/8730e2ff-d6bf-4a1a-8bc9-433c85d0eefe
-- title:
--   Edge Extension: le extend Param
-- statement:
--   The Edge Extension construction uses the le extend Param property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L396-L403
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L396-L403

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

theorem BKAR.Forest.EdgeExtension.le_extendParam (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) (e : F'.EdgeParam) :
    s ≤ h.extendParam u s e := by sorry
