-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_interpWithFill_extend_eq
-- name    : BKAR.Forest.EdgeExtension.interpWithFill_extend_eq
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:19:18.162387+00:00
-- url     : https://prove2.me/theorems/c463995f-fa1d-4a3f-b57b-e69c05b68501
-- title:
--   Edge Extension: interp With Fill extend eq
-- statement:
--   Ordered-step reinterpretation: if the newly-added edge receives the current
--   global parameter `s`, and all old forest parameters are at least `s`, then the
--   old and extended fill-parameter configurations agree at `s`.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L418-L449
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L418-L449

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

theorem BKAR.Forest.EdgeExtension.interpWithFill_extend_eq (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) {s : ℝ}
    (hu : ∀ e : F.EdgeParam, s ≤ u e) :
    F.interpWithFill u s = F'.interpWithFill (h.extendParam u s) s := by sorry
