-- Prove2me | Theorems.Thm_BKAR_mixedPartialList_nil_apply
-- name    : BKAR.mixedPartialList_nil_apply
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:19:57.6302+00:00
-- url     : https://prove2.me/theorems/04427472-1383-4ad2-967c-c473e65ecf54
-- title:
--   BKAR: mixed Partial List nil apply
-- statement:
--   The BKAR construction uses the mixed Partial List nil apply property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L111-L114
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/PartialDeriv.lean#L111-L114

import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Pi
import Definitions.Def_BKAR_Interpolation
import Definitions.Def_BKAR_PartialDeriv
set_option autoImplicit false
open BKAR
variable {V : Type*} [DecidableEq V]

theorem BKAR.mixedPartialList_nil_apply (ρ : (Edge V → ℝ) → ℝ)
    (x : Edge V → ℝ) :
    mixedPartialList ([] : List (Edge V)) ρ x = ρ x := by sorry

attribute [defeq] BKAR.mixedPartialList_nil_apply
