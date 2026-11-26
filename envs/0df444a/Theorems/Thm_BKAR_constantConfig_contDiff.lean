-- Prove2me | Theorems.Thm_BKAR_constantConfig_contDiff
-- name    : BKAR.constantConfig_contDiff
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:23.926612+00:00
-- url     : https://prove2.me/theorems/b5c3dcea-94b8-4f8d-8543-0036104976b6
-- title:
--   BKAR: constant Config cont Diff
-- statement:
--   The BKAR construction uses the constant Config cont Diff property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L213-L218
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L213-L218

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

theorem BKAR.constantConfig_contDiff :
    ContDiff ℝ (∞ : WithTop ℕ∞) (constantConfig (V := V)) := by sorry
