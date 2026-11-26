-- Prove2me | Theorems.Thm_BKAR_Forest_EdgeExtension_extendParam_new
-- name    : BKAR.Forest.EdgeExtension.extendParam_new
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:59.043302+00:00
-- url     : https://prove2.me/theorems/cd5a59ce-590a-4807-a47f-3c4d96833cdf
-- title:
--   Edge Extension: extend Param new
-- statement:
--   The Edge Extension construction uses the extend Param new property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L370-L373
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L370-L373

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
import Theorems.Thm_BKAR_Forest_EdgeExtension_new_mem

set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.Forest.EdgeExtension
variable {F F' : Forest V} {e₀ : Edge V}

theorem BKAR.Forest.EdgeExtension.extendParam_new (h : EdgeExtension F F' e₀)
    (u : F.EdgeParam → ℝ) (s : ℝ) :
    h.extendParam u s ⟨e₀, h.new_mem⟩ = s := by sorry
