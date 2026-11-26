-- Prove2me | Theorems.Thm_BKAR_mixedPartialList_cons
-- name    : BKAR.mixedPartialList_cons
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:43.732429+00:00
-- url     : https://prove2.me/theorems/9d68d8e0-b5df-4175-99f9-77801ec6a6f4
-- title:
--   BKAR: mixed Partial List cons
-- statement:
--   The BKAR construction uses the mixed Partial List cons property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L117-L120
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L117-L120

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.mixedPartialList_cons (e : Edge V) (es : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    mixedPartialList (e :: es) ρ = partialDeriv e (mixedPartialList es ρ) := by sorry

attribute [defeq] BKAR.mixedPartialList_cons
