-- Prove2me | Theorems.Thm_BKAR_Forest_mixedPartial_empty_edges_apply
-- name    : BKAR.Forest.mixedPartial_empty_edges_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:24:28.737837+00:00
-- url     : https://prove2.me/theorems/b8078450-ba45-5b20-84ef-db52465924d4
-- title:
--   Forest: mixed Partial empty edges apply
-- statement:
--   The Forest construction uses the mixed Partial empty edges apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L162-L165
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L162-L165

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

theorem BKAR.Forest.mixedPartial_empty_edges_apply (hF : F.edges = ∅)
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) :
    F.mixedPartial ρ x = ρ x := by sorry
