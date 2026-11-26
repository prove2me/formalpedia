-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_intervalIntegrable_comp
-- name    : BKAR.BKARContDiff.mixedPartialList_intervalIntegrable_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:51.438003+00:00
-- url     : https://prove2.me/theorems/78dc8f15-64be-5e0a-bc5d-fdb5efe64396
-- title:
--   BKARCont Diff: mixed Partial List interval Integrable comp
-- statement:
--   The BKARCont Diff construction uses the mixed Partial List interval Integrable comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L102-L108
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L102-L108

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

theorem BKAR.BKARContDiff.mixedPartialList_intervalIntegrable_comp (hρ : BKARContDiff ρ)
    (es : List (Edge V)) {γ : ℝ → Edge V → ℝ}
    (hγ : Continuous γ) (a b : ℝ) :
    IntervalIntegrable
      (fun t : ℝ => BKAR.mixedPartialList es ρ (γ t))
      MeasureTheory.volume a b := by sorry
