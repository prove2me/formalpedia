-- Prove2me | Theorems.Thm_BKAR_partialDeriv_eq_deriv
-- name    : BKAR.partialDeriv_eq_deriv
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:19:35.293723+00:00
-- url     : https://prove2.me/theorems/6f2c01e4-e946-50ed-8463-c180b692ae5e
-- title:
--   BKAR: partial Deriv eq deriv
-- statement:
--   The BKAR construction uses the partial Deriv eq deriv property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L68-L72
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L68-L72

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.partialDeriv_eq_deriv (e : Edge V)
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) :
    partialDeriv e ρ x =
      deriv (fun t : ℝ => ρ (updateCoord x e t)) (x e) := by sorry
