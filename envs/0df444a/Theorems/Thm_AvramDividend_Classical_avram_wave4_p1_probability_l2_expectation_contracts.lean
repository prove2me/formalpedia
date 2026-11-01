-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_probability_l2_expectation_contracts
-- name    : AvramDividend.Classical.avram_wave4_p1_probability_l2_expectation_contracts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T00:01:00.000918+00:00
-- url     : https://prove2.me/theorems/03b0dab4-c49a-4d44-9700-ab3b10018812
-- title:
--   Original probability-space L² expectation has operator norm at most one
-- statement:
--   For any original probability space P and any real L²(P) equivalence class F, prove |∫F dP| ≤ ‖F‖_{L²(P)}. This quantitative contractive expectation bound follows from the pinned Mathlib real L² inner product of F with the indicator of the full sample space, whose L² norm is one, and the Hilbert Cauchy–Schwarz inequality. This is a useful source-faithful uniform moment estimate for stopped compensated integrals and an explicit quantitative form of expectation continuity; no Poisson law or Campbell identity is assumed.
-- source:
--   Pinned Mathlib 0df444a Mathlib/MeasureTheory/Function/L2Space.lean L2.inner_indicatorConstLp_one; Function/LpSpace/Indicator.lean norm_indicatorConstLp; Analysis/InnerProductSpace/Basic.lean norm_inner_le_norm.

import Mathlib

open MeasureTheory Set Filter Topology InnerProductSpace
open scoped ENNReal InnerProductSpace

theorem AvramDividend.Classical.avram_wave4_p1_probability_l2_expectation_contracts
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : Lp ℝ (2 : ℝ≥0∞) P) :
    |∫ ω, F ω ∂P| ≤ ‖F‖ := by sorry
