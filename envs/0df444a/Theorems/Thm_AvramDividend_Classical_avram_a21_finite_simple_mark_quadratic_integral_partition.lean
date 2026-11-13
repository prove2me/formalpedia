-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a21_finite_simple_mark_quadratic_integral_partition
-- name    : AvramDividend.Classical.avram_a21_finite_simple_mark_quadratic_integral_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:16:55.444211+00:00
-- url     : https://prove2.me/theorems/dcc8d839-f4d1-4cee-b54e-3ce2629526fa
-- title:
--   Integral of a finite simple mark squared equals its squared fibre-weight intensity sum
-- statement:
--   For any measure ν and measurable Borel region S of finite ν-mass, the integral of the square of a real-valued finite simple mark u equals the finite sum of squared mark values times the ν-masses of the disjoint Borel fibres S∩u^{-1}({y}). This deterministic identity is needed to convert exact original Lévy source finite-valued raw marked moments into the bounded marked integral isometry; it does not change the original process or probability space.
-- source:
--   Mathlib finite simple function fibre decomposition and Bochner integral_indicator_const, integral_finset_sum. Related Proved 4c87924a but squares are handled directly without the potential noninjectivity of x→x².

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a21_finite_simple_mark_quadratic_integral_partition
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (hMass : ν S < ⊤) (u : SimpleFunc ℝ ℝ) :
    (∫ z in S, (u z) ^ 2 ∂ν) =
      ∑ y ∈ u.range, y ^ 2 * (ν (S ∩ u ⁻¹' {y})).toReal := by sorry
