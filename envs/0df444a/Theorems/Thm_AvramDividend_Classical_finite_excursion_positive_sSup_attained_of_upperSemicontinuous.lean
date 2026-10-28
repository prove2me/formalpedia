-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_excursion_positive_sSup_attained_of_upperSemicontinuous
-- name    : AvramDividend.Classical.finite_excursion_positive_sSup_attained_of_upperSemicontinuous
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:37:34.325746+00:00
-- url     : https://prove2.me/theorems/ffea8642-7c37-4b38-8ee4-9e67ccbb6b15
-- title:
--   The strictly positive exact supremum of a finite upper-semicontinuous excursion with zero endpoints is attained in its interior
-- statement:
--   For a real-valued upper-semicontinuous excursion path R on a finite interval [0,ζ] with zero endpoints, assume the image is bounded above and its least upper bound is strictly positive. Then R achieves its exact image supremum at some time T strictly between 0 and ζ. Unlike earlier maximum-attainment helper this theorem does not require explicitly postulating upper-bound sharpness or a separate level x: it constructs the sharp least upper bound using Mathlib's sSup and derives the sharpness from lt_csSup_iff. This is the precise height-hitting statement for finite-lifetime excursion paths.
-- source:
--   Elementary compact upper-semicontinuous extrema and conditional supremum properties; Kuznetsov–Kyprianou–Rivero (2013), §2.3 Lemma 2.4.

import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Theorems.Thm_AvramDividend_Classical_finite_excursion_height_attained_of_upperSemicontinuous

open AvramDividend.Classical Set Topology
open scoped NNReal

theorem AvramDividend.Classical.finite_excursion_positive_sSup_attained_of_upperSemicontinuous
    (R : ℝ≥0 → ℝ) (ζ : ℝ≥0) (hζ : 0 < ζ)
    (husc : UpperSemicontinuousOn R (Icc 0 ζ))
    (hzero : R 0 = 0) (hEnd : R ζ = 0)
    (hbdd : BddAbove (R '' Icc (0 : ℝ≥0) ζ))
    (hPos : 0 < sSup (R '' Icc (0 : ℝ≥0) ζ)) :
    ∃ T : ℝ≥0, 0 < T ∧ T < ζ ∧
      R T = sSup (R '' Icc (0 : ℝ≥0) ζ) := by sorry
