-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f8_integrable_clock_family_expected_iff_signed_witness
-- name    : AvramDividend.Classical.avram_p4_f8_integrable_clock_family_expected_iff_signed_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T10:01:24.82431+00:00
-- url     : https://prove2.me/theorems/19e00906-9417-4aa1-905f-cd3995473180
-- title:
--   Integrable family of exact stopped rewards has signed residual witnesses exactly when each expectation is below the barrier
-- statement:
--   For integrable random stopped rewards at each original physical localisation clock on a probability space, a uniform expected-value upper bound is equivalent to existence of an integrable non-positive-mean residual majorising every stopped reward. This is the exact algebraic adapter needed to pass from physical stopped Ito expectation estimates to source witness families; no stochastic UI premise is added.
-- source:
--   Source-exact scalar compact clock expectation-to-signed witness equivalence, intended for the original X+D finite clock family; abstracted only over the random rewards and probability integral.

import Mathlib
open MeasureTheory

theorem AvramDividend.Classical.avram_p4_f8_integrable_clock_family_expected_iff_signed_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (hFI : ∀ k, Integrable (F k) P)
    (b : ℝ) :
    (∀ k, (∫ ω, F k ω ∂P) ≤ b) ↔
      ∃ M : ℕ → Ω → ℝ,
        (∀ k, Integrable (M k) P) ∧
        (∀ k, (∫ ω, M k ω ∂P) ≤ 0) ∧
        (∀ k, ∀ᵐ ω ∂P, F k ω ≤ b + M k ω) := by sorry
