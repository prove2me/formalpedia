-- Prove2me | Theorems.Thm_BKAR_intervalIntegral_continuous_primitive_of_continuous
-- name    : BKAR.intervalIntegral_continuous_primitive_of_continuous
-- status  : Proved
-- author  : @marwahaha
-- created : 2026-11-26T08:23:20.398829+00:00
-- url     : https://prove2.me/theorems/9d794d26-23ae-5612-adf9-7217a6542a9b
-- title:
--   BKAR: interval Integral continuous primitive of continuous
-- statement:
--   A continuous one-dimensional integrand has a continuous moving-upper-bound primitive.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L113-L117
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L113-L117

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

theorem BKAR.intervalIntegral_continuous_primitive_of_continuous
    {f : ℝ → ℝ} (hf : Continuous f) (a : ℝ) :
    Continuous (fun b : ℝ => ∫ t in a..b, f t) := by sorry
