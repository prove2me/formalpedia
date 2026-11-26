-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_continuous
-- name    : BKAR.BKARContDiff.mixedPartialList_continuous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:25:34.569797+00:00
-- url     : https://prove2.me/theorems/0f1a608c-9df6-47ec-bceb-bb907860fee4
-- title:
--   BKARCont Diff: mixed Partial List continuous
-- statement:
--   The BKARCont Diff construction uses the mixed Partial List continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L86-L89
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L86-L89

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

theorem BKAR.BKARContDiff.mixedPartialList_continuous (hρ : BKARContDiff ρ)
    (es : List (Edge V)) :
    Continuous (BKAR.mixedPartialList es ρ) := by sorry
