-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_reuse8_nonintegrable_drift_grid_expected_upper
-- name    : AvramDividend.Classical.avram_reuse8_nonintegrable_drift_grid_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T23:32:57.096443+00:00
-- url     : https://prove2.me/theorems/74c3a3a2-ab59-42f4-a180-45a731310e8e
-- title:
--   Finite-grid original payoff expected upper bound without requiring absolute drift integrability
-- statement:
--   A nonnegative measurable dividend-grid payoff lies below initial value plus an integrable mean-zero martingale, an almost-everywhere nonpositive potentially nonintegrable generator drift and an integrable positive truncation error. Then the payoff is integrable and its expectation is bounded by the initial value plus the expectation of the positive error, without assuming the generator drift is integrable.
-- source:
--   Source-independent one-sided finance/measure bridge for original BV physical-grid route 07d7e4be and 4612f9a8. The exact Lévy grid identity, zero-mean compensator, original drift sign and vanishing expected positive error remain source-specific independent obligations; no claim of generator-cell absolute L1 is made.

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_reuse8_nonintegrable_drift_grid_expected_upper
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (b : ℝ) (F M B E : ℕ → Ω → ℝ)
    (hFmeas : ∀ n, Measurable (F n))
    (hFnonneg : ∀ n, 0 ≤ᵐ[P] F n)
    (hMI : ∀ n, Integrable (M n) P)
    (hM0 : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hEI : ∀ n, Integrable (fun ω => max (E n ω) 0) P)
    (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPhysical : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ b + M n ω + B n ω + max (E n ω) 0) :
    ∀ n, Integrable (F n) P ∧
      (∫ ω, F n ω ∂P) ≤
        b + (∫ ω, max (E n ω) 0 ∂P) := by sorry
