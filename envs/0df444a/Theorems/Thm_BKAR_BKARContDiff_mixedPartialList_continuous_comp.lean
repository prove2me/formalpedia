-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_mixedPartialList_continuous_comp
-- name    : BKAR.BKARContDiff.mixedPartialList_continuous_comp
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:54.185804+00:00
-- url     : https://prove2.me/theorems/43782e83-9950-5664-b0e1-b1fcec179ca4
-- title:
--   BKARCont Diff: mixed Partial List continuous comp
-- statement:
--   The BKARCont Diff construction uses the mixed Partial List continuous comp property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L96-L100
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L96-L100

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

theorem BKAR.BKARContDiff.mixedPartialList_continuous_comp (hρ : BKARContDiff ρ)
    (es : List (Edge V)) {γ : ℝ → Edge V → ℝ}
    (hγ : Continuous γ) :
    Continuous (fun t : ℝ => BKAR.mixedPartialList es ρ (γ t)) := by sorry
