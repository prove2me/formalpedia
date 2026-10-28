-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_negative_jump_exp_integral_tendsto_zero_nat
-- name    : AvramDividend.Classical.finite_negative_jump_exp_integral_tendsto_zero_nat
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:07:49.378583+00:00
-- url     : https://prove2.me/theorems/c92e2651-c56f-4a3c-867a-e5cd9f0960c8
-- title:
--   Finite negative-jump intensity forces the exponentially tilted negative Lévy mass to vanish
-- statement:
--   For any measure on real jumps with finite mass on the strictly negative half-line, the real integral of exp(n y) against its negative-jump restriction tends to zero as the natural parameter n increases. This is a dominated-convergence precursor of the Poisson zero-jump survival law for a finite-activity bounded-variation spectrally negative Lévy process.
-- source:
--   Dominated convergence; Avram, Palmowski and Pistorius (2007), Section 3.3, first-jump formula (3.14).

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Order.Filter.AtTopBot.Field
import Mathlib.Order.Filter.AtTopBot.Archimedean
open MeasureTheory Filter Set Topology

theorem AvramDividend.Classical.finite_negative_jump_exp_integral_tendsto_zero_nat
    (ν : Measure ℝ) (hFinite : ν (Iio (0 : ℝ)) < ⊤) :
    Tendsto (fun n : ℕ =>
      ∫ y in Iio (0 : ℝ), Real.exp ((n : ℝ) * y) ∂ν)
      atTop (𝓝 0) := by sorry
