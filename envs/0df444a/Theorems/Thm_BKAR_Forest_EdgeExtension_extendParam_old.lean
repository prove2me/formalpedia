-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_old
-- name    : BKAR.Forest.EdgeExtension.extendParam_old
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:16:13.376426+00:00
-- url     : https://prove2.me/theorems/e3ae19bc-8283-4ca0-bffa-7b3a86d7573f
-- title:
--   Edge Extension: extend Param old
-- statement:
--   The Edge Extension construction uses the extend Param old property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L375-L382
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L375-L382

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_EdgeExtension_old_mem

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}

theorem BKAR.Forest.EdgeExtension.extendParam_old (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (s : ℝ) {e : Edge V} (he : e ∈ F.edges) :
    h.extendParam u s ⟨e, h.old_mem he⟩ = u ⟨e, he⟩ := by sorry
