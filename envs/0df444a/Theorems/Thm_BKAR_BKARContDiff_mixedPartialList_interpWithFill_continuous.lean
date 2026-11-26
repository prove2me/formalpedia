-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_interpWithFill_continuous
-- name    : BKAR.BKARContDiff.mixedPartialList_interpWithFill_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:26:35.205351+00:00
-- url     : https://prove2.me/theorems/d2675e30-93de-45d7-b3cd-04f358e32243
-- title:
--   BKARCont Diff: mixed Partial List interp With Fill continuous
-- statement:
--   The BKARCont Diff construction uses the mixed Partial List interp With Fill continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L404-L411
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L404-L411

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

theorem BKAR.BKARContDiff.mixedPartialList_interpWithFill_continuous
    {ρ : (Edge V → ℝ) → ℝ}
    (hρ : BKARContDiff ρ) (es : List (Edge V))
    (F : Forest V) (u : F.EdgeParam → ℝ) :
    Continuous
      (fun t : ℝ => BKAR.mixedPartialList es ρ
        (F.interpWithFill u t)) := by sorry
