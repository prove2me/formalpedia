-- Prove2me | Theorems.Thm_BKAR_BKARContDiff_continuous
-- name    : BKAR.BKARContDiff.continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:22:45.433191+00:00
-- url     : https://prove2.me/theorems/9c30952f-3e4a-4622-8b5f-4724249db5a2
-- title:
--   BKARCont Diff: continuous
-- statement:
--   The BKARCont Diff construction uses the continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L45-L47
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L45-L47

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

theorem BKAR.BKARContDiff.continuous (hρ : BKARContDiff ρ) :
    Continuous ρ := by sorry
