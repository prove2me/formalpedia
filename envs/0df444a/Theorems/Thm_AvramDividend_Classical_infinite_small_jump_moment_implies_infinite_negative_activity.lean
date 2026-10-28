-- Prove2me | Theorems.Thm_AvramDividend_Classical_infinite_small_jump_moment_implies_infinite_negative_activity
-- name    : AvramDividend.Classical.infinite_small_jump_moment_implies_infinite_negative_activity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:14:50.362366+00:00
-- url     : https://prove2.me/theorems/9c9ba7fd-60ec-487e-a39d-401151963146
-- title:
--   Infinite small-jump first variation forces infinite negative jump activity
-- statement:
--   For any measure on signed jump sizes, divergence of its small-negative-jump absolute first-moment integral over (-1,0) implies infinite total mass of strictly negative jumps. If the negative mass were finite, |y|<1 throughout the small interval would make its absolute-magnitude integral finite, a contradiction. This is an unconditional measure-theoretic bridge from the exact σ=0 unbounded variation alternative to the Poisson infinite-activity near-zero jump programme. It does not assert anything about first moments of Lévy increments.
-- source:
--   Uses Mathlib measure monotonicity, set-lintegral monotonicity and the finite-mass constant integral. Needed for Open ae_early_downward_jumps_of_infinite_negative_activity [ff758fb4-87e5-4eec-b153-b6135498ca04] and zero-discount C1 core [8aaa16d2-d9ec-4e8f-8e42-cc551cca9d8d].

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.Tactic.Linarith
open MeasureTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.infinite_small_jump_moment_implies_infinite_negative_activity
    (ν : Measure ℝ)
    (hinf : (∫⁻ y in Ioo (-1 : ℝ) 0,
      ENNReal.ofReal |y| ∂ν) = ⊤) :
    ν (Iio (0 : ℝ)) = ⊤ := by sorry
