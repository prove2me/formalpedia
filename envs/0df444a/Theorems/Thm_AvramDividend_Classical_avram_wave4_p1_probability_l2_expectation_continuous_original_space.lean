-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_probability_l2_expectation_continuous_original_space
-- name    : AvramDividend.Classical.avram_wave4_p1_probability_l2_expectation_continuous_original_space
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T23:56:10.320217+00:00
-- url     : https://prove2.me/theorems/d2c2ff3c-9bb4-44f4-a158-a327ccc7a8a7
-- title:
--   Expectation of L² random variables is continuous on the original probability space
-- statement:
--   For any original probability space with its given measure, the map sending an L² equivalence class F to its actual Bochner expectation ∫ F dP is continuous. The proof represents expectation as the real Hilbert L² inner product against the constant-one function, using the pinned Mathlib L2.inner_indicatorConstLp_eq_inner_setIntegral theorem and continuity of the inner product. There is no stochastic Poisson or martingale premise. This directly supplies the continuous expectation-functional hypothesis of the already-Proved P1 centered stopped L² limit theorem b028e313, without replacing the original probability space.
-- source:
--   Pinned Mathlib 0df444a: Mathlib/MeasureTheory/Function/L2Space.lean L2.inner_indicatorConstLp_eq_inner_setIntegral, real_inner_smul_right, real_inner_self_eq_norm_sq, Continuous.inner.

import Mathlib

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal InnerProductSpace

theorem AvramDividend.Classical.avram_wave4_p1_probability_l2_expectation_continuous_original_space
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] :
    Continuous (fun F : Lp ℝ (2 : ℝ≥0∞) P => ∫ ω, F ω ∂P) := by sorry
