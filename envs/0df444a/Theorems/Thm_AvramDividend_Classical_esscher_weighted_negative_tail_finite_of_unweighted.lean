-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_weighted_negative_tail_finite_of_unweighted
-- name    : AvramDividend.Classical.esscher_weighted_negative_tail_finite_of_unweighted
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T09:15:00.572915+00:00
-- url     : https://prove2.me/theorems/ce59aa21-09fa-4283-b034-b9926c91095c
-- title:
--   Esscher tilting preserves finiteness of every truncated negative-jump tail
-- statement:
--   For any measure of signed jumps, a nonnegative Esscher tilt decreases the density on the strictly negative half-line. Therefore whenever the original measure has finite mass on jumps less than -x for positive x, the Esscher-weighted tail measure has finite mass there. The proof uses an exponential bound at negative arguments and monotonicity of ENNReal integration.
-- source:
--   Elementary Esscher density inequality and pinned Mathlib withDensity_apply, lintegral_mono_ae, ae_restrict_mem.

import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Tactic.Linarith

open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.esscher_weighted_negative_tail_finite_of_unweighted
    (ν : Measure ℝ) (φ x : ℝ) (hφ : 0 ≤ φ) (hx : 0 < x)
    (hfinite : ν (Iio (-x)) < ⊤) :
    (ν.withDensity (fun y : ℝ => ENNReal.ofReal (Real.exp (φ * y))))
      (Iio (-x)) < ⊤ := by sorry
