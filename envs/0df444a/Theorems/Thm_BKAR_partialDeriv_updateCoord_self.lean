-- Prove2me | Theorems.Thm_BKAR_partialDeriv_updateCoord_self
-- name    : BKAR.partialDeriv_updateCoord_self
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:19:37.15328+00:00
-- url     : https://prove2.me/theorems/7e025d97-becf-503b-a4c5-dce4fd5c4bcf
-- title:
--   BKAR: partial Deriv update Coord self
-- statement:
--   The BKAR construction uses the partial Deriv update Coord self property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L74-L81
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L74-L81

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.partialDeriv_updateCoord_self (e : Edge V)
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) (s : ℝ) :
    partialDeriv e ρ (updateCoord x e s) =
      deriv (fun t : ℝ => ρ (updateCoord x e t)) s := by sorry
