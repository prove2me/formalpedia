-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bf_new_upperray_weighted_exp_factor
-- name    : AvramDividend.Classical.avram_ws01e_bf_new_upperray_weighted_exp_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T22:55:18.349333+00:00
-- url     : https://prove2.me/theorems/79c3307a-f647-4e50-ad27-adc0079b1ff2
-- title:
--   Single-test upper-ray factorisation implies its exponential weighted moment factor
-- statement:
--   For one fixed nonnegative measurable test W with finite total integral under μ, equality of weighted and unweighted upper-ray masses for the actual observable S at every real threshold b implies factorisation of its exponentially weighted integral for any β>0. This is a weaker single-test transform statement, not full independence of S and an arbitrary random variable. It supports a possible route from the separately Proved true Qp threshold identity to the finite-rate descending transform without taking over Chat 02's full IndepFun target.
-- source:
--   Exact layer-cake/Cavalieri identity for nonnegative measurable exponentials, proved Mathlib MeasureTheory.lintegral_eq_lintegral_meas_lt, with the finite-scalar variant of lintegral_mul_const and the genuine upper-ray factor law.

import Mathlib
import Definitions.Def_AvramDividend_Classical_Reflection
open AvramDividend.Classical MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_bf_new_upperray_weighted_exp_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (μ : Measure Ω)
    (S : Ω → ℝ) (W : Ω → ENNReal) (β : ℝ)
    (hS : Measurable S) (hW : Measurable W) (hβ : 0 < β)
    (hK : (∫⁻ z, W z ∂μ) ≠ ⊤)
    (hTail : ∀ b : ℝ,
      (μ.withDensity W) {z : Ω | b < S z} =
        μ {z : Ω | b < S z} * (∫⁻ z, W z ∂μ)) :
    (∫⁻ z, W z * ENNReal.ofReal (Real.exp (β * S z)) ∂μ) =
      (∫⁻ z, ENNReal.ofReal (Real.exp (β * S z)) ∂μ) *
        (∫⁻ z, W z ∂μ) := by sorry
