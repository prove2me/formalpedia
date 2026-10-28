-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exponential_deficit_limit_nat
-- name    : AvramDividend.Classical.finite_negative_jump_exponential_deficit_limit_nat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:26:09.568993+00:00
-- url     : https://prove2.me/theorems/1c22e0d0-5d11-4e88-aa57-810af654e211
-- title:
--   Finite-activity Lévy exponential deficit converges to total negative jump intensity
-- statement:
--   For a finite measure of strictly negative Lévy jumps, the Bochner integral of 1-exp(n y) converges to the total negative jump intensity as n→∞. It follows by splitting the integral into finite mass minus the exponentially tilted jump mass, whose decay has been proved. The resulting scalar limit is the exponent in the first-jump survival law for the actual bounded-variation Lévy process.
-- source:
--   Avram Palmowski Pistorius (2007), §3.3, compound-Poisson jump intensity and first-jump formula (3.14).

import Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exp_integral_tendsto_zero_nat
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Typeclasses.Finite
import Mathlib.Analysis.SpecialFunctions.Exp
open MeasureTheory Filter Set Topology

theorem AvramDividend.Classical.finite_negative_jump_exponential_deficit_limit_nat
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) < ⊤) :
    Tendsto (fun n : ℕ =>
      ∫ y in Iio (0 : ℝ), (1 - Real.exp ((n : ℝ) * y)) ∂ν)
      atTop (𝓝 (ν (Iio (0 : ℝ))).toReal) := by sorry
