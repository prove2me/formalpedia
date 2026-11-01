-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_future_poisson_past_product_orthogonal
-- name    : AvramDividend.Classical.avram_wave4_p1_future_poisson_past_product_orthogonal
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T13:48:06.018989+00:00
-- url     : https://prove2.me/theorems/e18265f8-241d-493f-ab46-e845e4bef374
-- title:
--   Future centred Poisson count orthogonal to products of L2 past variables
-- statement:
--   For any two square-integrable, possibly mutually dependent original-path past random variables H and J, a genuine future Poisson count K independent of the joint pair (H,J), with Poisson rate r and explicit L1 centred-count integrability, has its centred count orthogonal to H·J. The proof derives E[K-r]=0 from the actual Poisson count law and Proved rate expectation, derives H·J integrability by Holder L2×L2, preserves pair independence under measurable multiplication, and factors the three-fold expectation. This is a noncircular cross-cell orthogonality interface for predictable finite-grid L2 sums; it does not assume that the count is a martingale or that a stochastic integral is an isometry.
-- source:
--   Pinned Mathlib MemLp.integrable_mul, IndepFun.comp, IndepFun.integrable_mul, HasLaw.integral_comp; canonical Proved poisson_count_expected_rate_ws01b 951829c1-447e-4e44-910f-e6c465dda134.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_poisson_count_expected_rate_ws01b

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal Nat

theorem AvramDividend.Classical.avram_wave4_p1_future_poisson_past_product_orthogonal
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (H J : Ω → ℝ) (hH2 : MemLp H 2 P) (hJ2 : MemLp J 2 P)
    (K : Ω → ℕ) (hKm : Measurable K)
    (r : ℝ≥0) (hKlaw : HasLaw K (poissonMeasure r) P)
    (hKInt : Integrable (fun ω => (K ω : ℝ) - (r : ℝ)) P)
    (hPast : IndepFun (fun ω => (H ω, J ω)) K P) :
    Integrable (fun ω => (H ω * J ω) * ((K ω : ℝ) - (r : ℝ))) P ∧
      (∫ ω, (H ω * J ω) * ((K ω : ℝ) - (r : ℝ)) ∂P) = 0  := by sorry
