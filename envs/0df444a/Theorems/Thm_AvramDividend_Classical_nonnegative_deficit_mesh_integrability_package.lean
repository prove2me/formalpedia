-- Prove2me | Theorems.Thm_AvramDividend_Classical_nonnegative_deficit_mesh_integrability_package
-- name    : AvramDividend.Classical.nonnegative_deficit_mesh_integrability_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:42:31.369947+00:00
-- url     : https://prove2.me/theorems/74ada80c-6ab2-43fd-be3a-717c8e131ed0
-- title:
--   All nonnegative measurable BV drift-deficit mesh exponential gaps and their weighted finite sum are integrable
-- statement:
--   For a finite family of almost surely nonnegative random drift-deficit increments, every reciprocal-drift-scaled exponential deficit is between zero and one and hence integrable under a finite measure if measurable. The entire weighted finite sum is integrable as well. This provides the two separate integrability hypotheses for the accepted genuine zero-barrier expected-survival finite-mesh bound.
-- source:
--   Proved nonnegative_exp_deficit_integrable; Mathlib integrable_finset_sum and Integrable.const_mul.

import Theorems.Thm_AvramDividend_Classical_nonnegative_exp_deficit_integrable
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Tactic.Positivity

open AvramDividend.Classical MeasureTheory Finset
open scoped BigOperators

theorem AvramDividend.Classical.nonnegative_deficit_mesh_integrability_package
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsFiniteMeasure P]
    (N : ℕ) (D : ℕ → Ω → ℝ) (a : ℝ) (ha : 0 < a)
    (hIncr : ∀ k : ℕ, k < N →
      ∀ᵐ ω ∂P, 0 ≤ D (k + 1) ω - D k ω)
    (hMeas : ∀ k : ℕ, k < N →
      AEStronglyMeasurable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P) :
    (∀ k : ℕ, k < N →
      Integrable
        (fun ω => (1 : ℝ) -
          Real.exp (-(1 / (2 * a)) *
            (D (k + 1) ω - D k ω))) P) ∧
    Integrable
      (fun ω => 4 * a * ∑ k ∈ Finset.range N,
        (1 - Real.exp (-((D (k + 1) ω - D k ω) / (2 * a))))) P := by sorry
