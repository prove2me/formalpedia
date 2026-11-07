-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_centered_physical_error_signed_budget
-- name    : AvramDividend.Classical.avram_p3_grid4_centered_physical_error_signed_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:40:31.812531+00:00
-- url     : https://prove2.me/theorems/55073d4b-6f62-4d89-b9fd-486684927be3
-- title:
--   Centre the integrable original physical-grid error into the signed source without changing its nonpositive mean
-- statement:
--   Under the original probability measure P, centre any L1 nonnegative physical Taylor/contact error Err_n around its actual expectation. The corrected combined signed source Z_n+Err_n-E[Err_n] remains L1 and its expectation equals E[Z_n]≤0. A source pathwise budget with random Err_n thereby becomes one with deterministic slack E[Err_n], which vanishes under already proved error mean limits. This is compatible with the real original Lévy X/D and avoids demanding separate martingale/drift L1 bounds.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_centered_physical_error_signed_budget
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (Z Err : ℕ → Ω → ℝ)
    (hZ : ∀ n, Integrable (Z n) P ∧
      (∫ ω, Z n ω ∂P) ≤ 0)
    (hErr : ∀ n, Integrable (Err n) P) :
    ∀ n,
      Integrable (fun ω => Z n ω + Err n ω -
        (∫ ξ, Err n ξ ∂P)) P ∧
      (∫ ω, Z n ω + Err n ω -
        (∫ ξ, Err n ξ ∂P) ∂P) ≤ 0 := by sorry
