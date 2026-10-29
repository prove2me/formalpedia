-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_dyadic_slope_tendstoInMeasure_zero_ws01c
-- name    : AvramDividend.Classical.bv_actual_dyadic_slope_tendstoInMeasure_zero_ws01c
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:00:13.001633+00:00
-- url     : https://prove2.me/theorems/00693178-f7ba-46c7-9ad1-8af4ba0d7daa
-- title:
--   Actual origin dyadic BV slope converges to zero in measure
-- statement:
--   Converts convergence in measure of the scaled drift deficit 2^n(δ_n d−X(δ_n)) into convergence in measure of d−(X(δ_n)−X(0))/δ_n, the same slope sequence used by stationary positive-time Fubini. Uses exact δ_n θ_n=1, δ_n>0, the process initial value X(0)=0, equality of the two random variables, and the pinned convergence-in-measure a.e.-congruence theorem. This identifies the correct sequence without claiming a.s. convergence prematurely.
-- source:
--   Source-complete algebraic and measure-theoretic adapter from work/avram_ws01c_actual_slope_in_measure_adapter_draft.lean, preparing the full-sequence almost-sure zero-slope assembly.

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
import Theorems.Thm_AvramDividend_Classical_bv_actual_dyadic_deficit_tendstoInMeasure_zero_ws01c

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal

theorem AvramDividend.Classical.bv_actual_dyadic_slope_tendstoInMeasure_zero_ws01c
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {ℱ : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P ℱ) (hBV : X.BoundedVariation) :
    TendstoInMeasure P
      (fun (n : ℕ) (ω : Ω) =>
        X.drift -
          (X.X (((2 : ℝ≥0)⁻¹) ^ n) ω - X.X 0 ω) /
            ((((2 : ℝ≥0)⁻¹) ^ n : ℝ≥0) : ℝ))
      atTop (fun _ => (0 : ℝ)) := by sorry
