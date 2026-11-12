-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger143_measurable_residual_two_absolute_L1_errors_glue_positive
-- name    : AvramDividend.Classical.avram_gledger143_measurable_residual_two_absolute_L1_errors_glue_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T19:31:37.650609+00:00
-- url     : https://prove2.me/theorems/8335f1f0-3b4c-4d02-acd1-e2ba8be835ca
-- title:
--   Measurable integrable original residual with two absolute L1 errors has vanishing positive part
-- statement:
--   With an independently certified integrable positive residual and an exact pointwise source split, two vanishing absolute L1 errors imply the original positive residual has vanishing L1. The explicit integrability hypothesis repairs the missing measurability in the earlier overstrong gledger141 auxiliary.
-- source:
--   Source-specific residual integrability must be proved separately, in addition to clock and spatial absolute L1 limits; triangle inequality and finite-sum integral monotonicity provide the quantitative bound.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_gledger143_measurable_residual_two_absolute_L1_errors_glue_positive
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (S M G A B : ℕ → Ω → ℝ)
    (hAB : ∀ m ω, S m ω - M m ω - G m ω = A m ω + B m ω)
    (hI : ∀ m : ℕ, Integrable (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P)
    (hA : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => |A m ω|) P ∧
      (∫ ω, |A m ω| ∂P) ≤ ε)
    (hB : ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => |B m ω|) P ∧
      (∫ ω, |B m ω| ∂P) ≤ ε) :
    ∀ ε : ℝ, 0 < ε → ∃ k : ℕ, ∀ m : ℕ, k ≤ m →
      Integrable (fun ω => max (S m ω - M m ω - G m ω) (0 : ℝ)) P ∧
      (∫ ω, max (S m ω - M m ω - G m ω) (0 : ℝ) ∂P) ≤ ε := by sorry
