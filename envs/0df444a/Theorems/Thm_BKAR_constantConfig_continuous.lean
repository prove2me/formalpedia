-- Prove2me | Theorems.Thm_BKAR_constantConfig_continuous
-- name    : BKAR.constantConfig_continuous
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:26:00.738186+00:00
-- url     : https://prove2.me/theorems/046b0452-a351-567e-a10d-768168c64605
-- title:
--   BKAR: constant Config continuous
-- statement:
--   The BKAR construction uses the constant Config continuous property established by this source lemma. The formal statement records the complete hypotheses and conclusion.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L220-L222
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L220-L222

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

theorem BKAR.constantConfig_continuous :
    Continuous (constantConfig (V := V)) := by sorry
