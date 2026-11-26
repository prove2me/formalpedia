-- Prove2me | Theorems.Thm_BKAR_Forest_mixedPartial_def
-- name    : BKAR.Forest.mixedPartial_def
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:24:16.967053+00:00
-- url     : https://prove2.me/theorems/298c6cfc-e6e1-47c4-bb08-fb28d8ee61d2
-- title:
--   Forest: mixed Partial def
-- statement:
--   The Forest construction uses the mixed Partial def property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L151-L153
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L151-L153

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]
open BKAR.Forest
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (F : Forest V)

theorem BKAR.Forest.mixedPartial_def (ρ : (Edge V → ℝ) → ℝ) :
    F.mixedPartial ρ = mixedPartialList F.edges.toList ρ := by sorry
