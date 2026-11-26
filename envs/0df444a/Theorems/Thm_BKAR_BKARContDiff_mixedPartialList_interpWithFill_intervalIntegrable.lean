-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_interpWithFill_intervalIntegrable
-- name    : BKAR.BKARContDiff.mixedPartialList_interpWithFill_intervalIntegrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T09:05:43.736309+00:00
-- url     : https://prove2.me/theorems/44568e71-344f-407d-b9fb-27378e9f72c2
-- title:
--   BKARCont Diff: mixed Partial List interp With Fill interval Integrable
-- statement:
--   The BKARCont Diff construction uses the mixed Partial List interp With Fill interval Integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L413-L422
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L413-L422

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

theorem BKAR.BKARContDiff.mixedPartialList_interpWithFill_intervalIntegrable
    {ρ : (Edge V → ℝ) → ℝ}
    (hρ : BKARContDiff ρ) (es : List (Edge V))
    (F : Forest V) (u : F.EdgeParam → ℝ) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => BKAR.mixedPartialList es ρ
        (F.interpWithFill u t))
      MeasureTheory.volume a b := by sorry
