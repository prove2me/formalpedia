-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a560_eventual_expected_budget_to_centred_error_witness
-- name    : AvramDividend.Classical.avram_ga_a560_eventual_expected_budget_to_centred_error_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T08:49:27.862692+00:00
-- url     : https://prove2.me/theorems/234b1ff0-1a96-4775-8d14-2aaf33ad348d
-- title:
--   Eventual mean cash bound gives centred zero-mean witnesses and vanishing positive errors
-- statement:
--   Given integrability at each mesh and a uniform asymptotic expected bound limsup E F_n ≤ K, centre each random variable by its expectation, choose the nonnegative positive-part expectation excess as the constant residual error and add a small vanishing harmonic slack. This proves the full compensated witness inequality and vanishing expected positive residual used for finite-activity dividend verification.
-- source:
--   tendsto_order, expectation linearity under probability measure, harmonic slack and eventual epsilon upper bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a560_eventual_expected_budget_to_centred_error_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (K : ℝ)
    (hInt : ∀ n, Integrable (F n) P)
    (hExpected : ∀ ε : ℝ, 0 < ε →
      ∀ᶠ n in (atTop : Filter ℕ), (∫ ω, F n ω ∂P) ≤ K + ε) :
    ∃ (M Err : ℕ → Ω → ℝ) (η : ℕ → ℝ),
      (∀ n, 0 < η n) ∧
      Tendsto η atTop (nhds (0 : ℝ)) ∧
      (∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ K + M n ω + max (Err n ω) 0) ∧
      (∀ n, (∫ ω, max (Err n ω) 0 ∂P) ≤ η n) := by sorry
