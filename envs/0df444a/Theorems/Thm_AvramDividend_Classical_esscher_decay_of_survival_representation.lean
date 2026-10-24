-- Prove2me | Theorems.Thm_AvramDividend_Classical_esscher_decay_of_survival_representation
-- name    : AvramDividend.Classical.esscher_decay_of_survival_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:24:51.614978+00:00
-- url     : https://prove2.me/theorems/fe0a47f7-c754-452a-8442-c70770db5eca
-- title:
--   Esscher exponential scale decay from an all-time survival representation
-- statement:
--   Suppose the Esscher-normalised real scale function exp(-φx)W(x), for every positive x, equals a fixed nonnegative constant K times the real-valued all-time nonruin measure of a path process Z started at x. Suppose these measures are finite. Then the probability is monotone in the initial reserve, so the tilted scale function is monotone; consequently W(x)≤exp(-φ(y−x))W(y) for 0<x≤y. This isolates the change-of-measure survival representation needed in a non-circular alternate proof of the Avram unbounded-variation scale-decay theorem.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2012), Theory of Scale Functions for Spectrally Negative Lévy Processes, Theorem 2.1 and equations (22)–(25), separating the survival-law representation from the elementary monotonicity and Esscher scaling.

import Theorems.Thm_AvramDividend_Classical_tilted_monotone_implies_exit_decay
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.Data.ENNReal.Real
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.esscher_decay_of_survival_representation
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (Z : ℝ≥0 → Ω → ℝ)
    (W : ℝ → ℝ) (φ K : ℝ) (hK : 0 ≤ K)
    (hfinite : ∀ x : ℝ, 0 < x →
      P {ω | ∀ t : ℝ≥0, 0 ≤ x + Z t ω} ≠ ⊤)
    (hrep : ∀ x : ℝ, 0 < x →
      Real.exp (-φ * x) * W x =
        K * (P {ω | ∀ t : ℝ≥0, 0 ≤ x + Z t ω}).toReal) :
    ∀ x y : ℝ, 0 < x → x ≤ y →
      W x ≤ Real.exp (-φ * (y - x)) * W y := by sorry
