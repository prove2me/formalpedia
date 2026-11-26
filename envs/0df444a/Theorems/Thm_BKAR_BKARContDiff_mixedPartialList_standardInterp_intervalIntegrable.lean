-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_standardInterp_intervalIntegrable
-- name    : BKAR.BKARContDiff.mixedPartialList_standardInterp_intervalIntegrable
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T09:02:24.080897+00:00
-- url     : https://prove2.me/theorems/47bfe599-501a-51db-b700-1ad67852f03e
-- title:
--   BKARCont Diff: mixed Partial List standard Interp interval Integrable
-- statement:
--   The BKARCont Diff construction uses the mixed Partial List standard Interp interval Integrable property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L424-L434
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L424-L434

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

theorem BKAR.BKARContDiff.mixedPartialList_standardInterp_intervalIntegrable
    {ρ : (Edge V → ℝ) → ℝ}
    (hρ : BKARContDiff ρ) (es : List (Edge V))
    (F : Forest V) {uPath : ℝ → F.EdgeParam → ℝ}
    (hu : Continuous uPath) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => BKAR.mixedPartialList es ρ
        (F.standardInterp (uPath t)))
      MeasureTheory.volume a b := by sorry
