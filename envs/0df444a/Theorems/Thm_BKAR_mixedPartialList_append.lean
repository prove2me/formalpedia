-- Prove2me | Theorems.Thm_BKAR_mixedPartialList_append
-- name    : BKAR.mixedPartialList_append
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:24:12.884928+00:00
-- url     : https://prove2.me/theorems/e73a3a67-059c-581c-8228-77a9fa452253
-- title:
--   BKAR: mixed Partial List append
-- statement:
--   The BKAR construction uses the mixed Partial List append property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L129-L139
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L129-L139

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.mixedPartialList_append (es₁ es₂ : List (Edge V))
    (ρ : (Edge V → ℝ) → ℝ) :
    mixedPartialList (es₁ ++ es₂) ρ =
      mixedPartialList es₁ (mixedPartialList es₂ ρ) := by sorry
