-- Prove2me | Theorems.Thm_BKAR_intervalIntegral_primitive_intervalIntegrable_of_continuous
-- name    : BKAR.intervalIntegral_primitive_intervalIntegrable_of_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:25:41.283657+00:00
-- url     : https://prove2.me/theorems/3fc4cebd-b4cc-4cec-8cd6-8c61de58b4a0
-- title:
--   BKAR: interval Integral primitive interval Integrable of continuous
-- statement:
--   The moving-upper-bound primitive of a continuous one-dimensional integrand is integrable.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L120-L124
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L120-L124

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

theorem BKAR.intervalIntegral_primitive_intervalIntegrable_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) (a b c : ℝ) :
    IntervalIntegrable (fun x : ℝ => ∫ t in a..x, f t)
      MeasureTheory.volume b c := by sorry
