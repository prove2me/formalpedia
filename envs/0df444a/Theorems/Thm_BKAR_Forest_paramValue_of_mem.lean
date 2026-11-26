-- Prove2me | Theorems.Thm_BKAR_Forest_paramValue_of_mem
-- name    : BKAR.Forest.paramValue_of_mem
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:15:17.319297+00:00
-- url     : https://prove2.me/theorems/3ef05951-9a74-4a62-b8e5-8d7cc6ca6f00
-- title:
--   Forest: param Value of mem
-- statement:
--   The Forest construction uses the param Value of mem property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L64-L67
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Interpolation.lean#L64-L67

import Mathlib.Data.Real.Basic
import Definitions.Def_BKAR_Forest
import Definitions.Def_BKAR_Interpolation
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]

theorem BKAR.Forest.paramValue_of_mem (F : Forest V) (u : F.EdgeParam → ℝ)
    {e : Edge V} (he : e ∈ F.edges) :
    F.paramValue u e = u ⟨e, he⟩ := by sorry
