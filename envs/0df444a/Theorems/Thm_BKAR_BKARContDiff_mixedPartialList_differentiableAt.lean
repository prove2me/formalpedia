-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_differentiableAt
-- name    : BKAR.BKARContDiff.mixedPartialList_differentiableAt
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:25:45.858842+00:00
-- url     : https://prove2.me/theorems/44616909-436d-4176-a03d-144450550f7a
-- title:
--   BKARCont Diff: mixed Partial List differentiable At
-- statement:
--   The BKARCont Diff construction uses the mixed Partial List differentiable At property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L91-L94
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L91-L94

import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Data.List.GetD
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Definitions.Def_BKAR_PartialDeriv
import Definitions.Def_BKAR_Smoothness
set_option autoImplicit false
open scoped ContDiff
open BKAR
variable {V : Type*} [Fintype V] [DecidableEq V]
open BKAR.BKARContDiff
variable {ρ : (Edge V → ℝ) → ℝ}

theorem BKAR.BKARContDiff.mixedPartialList_differentiableAt (hρ : BKARContDiff ρ)
    (es : List (Edge V)) (x : Edge V → ℝ) :
    DifferentiableAt ℝ (BKAR.mixedPartialList es ρ) x := by sorry
