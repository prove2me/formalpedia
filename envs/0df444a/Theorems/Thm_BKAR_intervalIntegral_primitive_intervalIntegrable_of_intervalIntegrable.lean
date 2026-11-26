-- Prove2me | Theorems.Thm_BKAR_intervalIntegral_primitive_intervalIntegrable_of_intervalIntegrable
-- name    : BKAR.intervalIntegral_primitive_intervalIntegrable_of_intervalIntegrable
-- status  : Open
-- author  : @marwahaha
-- created : 2026-11-26T08:25:42.038904+00:00
-- url     : https://prove2.me/theorems/9705ea68-c1ee-56db-a3b1-4cf34caa0771
-- title:
--   BKAR: interval Integral primitive interval Integrable of interval Integrable
-- statement:
--   If an integrand is interval-integrable on `[a, b]`, then its moving primitive
--   from `a` is interval-integrable on the same interval.
--
--   Source: https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L130-L136
-- source:
--   https://github.com/scottnarmstrong/BKARForestFormula/blob/a07f44a534240fe6339558951dd78a19e4ef7c51/BKAR/Smoothness.lean#L130-L136

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

theorem BKAR.intervalIntegral_primitive_intervalIntegrable_of_intervalIntegrable
    {f : ℝ → ℝ} {a b : ℝ}
    (hf : IntervalIntegrable f MeasureTheory.volume a b) :
    IntervalIntegrable (fun x : ℝ => ∫ t in a..x, f t)
      MeasureTheory.volume a b := by sorry
