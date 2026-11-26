-- Prove2me | Theorems.Thm_BKAR_mixedPartialList_cons_apply
-- name    : BKAR.mixedPartialList_cons_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:20:45.876724+00:00
-- url     : https://prove2.me/theorems/d5492d0a-1363-41cf-a20f-0d72e13cfe4b
-- title:
--   BKAR: mixed Partial List cons apply
-- statement:
--   The BKAR construction uses the mixed Partial List cons apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L123-L127
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L123-L127

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.mixedPartialList_cons_apply (e : Edge V) (es : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) (x : Edge V → ℝ) :
    mixedPartialList (e :: es) ρ x =
      partialDeriv e (mixedPartialList es ρ) x := by sorry

attribute [defeq] BKAR.mixedPartialList_cons_apply
