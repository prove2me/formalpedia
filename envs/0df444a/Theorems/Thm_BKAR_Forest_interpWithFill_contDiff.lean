-- Prove2me | Theorems.Thm_BKAR_Forest_interpWithFill_contDiff
-- name    : BKAR.Forest.interpWithFill_contDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:39.007368+00:00
-- url     : https://prove2.me/theorems/2c6531c2-cd7c-4a32-83fb-a4e72595ba38
-- title:
--   Forest: interp With Fill cont Diff
-- statement:
--   The Forest construction uses the interp With Fill cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L286-L304
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L286-L304

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
open BKAR.Forest
variable (F : Forest V)

theorem BKAR.Forest.interpWithFill_contDiff (u : F.EdgeParam → ℝ) :
    ContDiff ℝ (∞ : WithTop ℕ∞) (F.interpWithFill u) := by sorry
