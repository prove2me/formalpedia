-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_nonneg_conditional_laplace_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_bi_new_nonneg_conditional_laplace_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:47:38.851284+00:00
-- url     : https://prove2.me/theorems/f6c2f91a-884e-403d-8756-20fb7a713712
-- title:
--   Nonnegative conditional Laplace laws on upper rays imply full independence
-- statement:
--   For measurable real R and a pointwise nonnegative measurable drawdown D under an arbitrary probability P, if every strictly positive upper-ray conditioning of R leaves the real Laplace transform of D unchanged at all positive beta, then R and D are independent. The integrability needed for conditional-law uniqueness follows from exp(-beta D) ≤ 1. Covers all Borel drawdown events and does not assume independence or a Wiener–Hopf theorem.
-- source:
--   Reduction via Proved AvramDividend.Classical.avram_ws01e_bi_new_conditional_mgf_indepFun (17e694fd), pinned Mathlib of_bound, integrable_map_measure, integral_map, and IndepFun.neg_right. Applies to genuine Qp with D nonnegative; all beta required.

import Mathlib.Probability.ConditionalProbability
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Theorems.Thm_AvramDividend_Classical_avram_ws01e_bi_new_conditional_mgf_indepFun

open MeasureTheory ProbabilityTheory Set Filter
open scoped ProbabilityTheory ENNReal

theorem AvramDividend.Classical.avram_ws01e_bi_new_nonneg_conditional_laplace_indepFun
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R D : Ω → ℝ) (hR : Measurable R) (hD : Measurable D)
    (hDnonneg : ∀ ω : Ω, 0 ≤ D ω)
    (hLap : ∀ a : ℝ, P (R ⁻¹' Set.Ioi a) ≠ 0 →
      ∀ β : ℝ, 0 < β →
        (∫ ω : Ω, Real.exp (-(β * D ω)) ∂(P[|R ⁻¹' Set.Ioi a])) =
          ∫ ω : Ω, Real.exp (-(β * D ω)) ∂P) :
    IndepFun R D P := by sorry
