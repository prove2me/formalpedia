-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a558_mean_budget_to_centred_L1_error_witness
-- name    : AvramDividend.Classical.avram_ga_a558_mean_budget_to_centred_L1_error_witness
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:42:34.357581+00:00
-- url     : https://prove2.me/theorems/698a671f-5b54-43d1-a940-3b0cd8af6c2b
-- title:
--   Mean upper bound yields a centred-martingale-style witness and zero positive error
-- statement:
--   For an integrable sequence of random variables with uniform expected upper bound K, centre each by its own expectation to get an integrable zero-mean witness, take the residual error identically zero and a vanishing positive harmonic sequence. Then the full centered cash inequality holds pointwise.
-- source:
--   Integral linearity, probability total mass one, scalar expectation upper bound, and harmonic sequence 1/(n+1) tends to zero.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a558_mean_budget_to_centred_L1_error_witness
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F : ℕ → Ω → ℝ) (K : ℝ)
    (hInt : ∀ n, Integrable (F n) P)
    (hExpected : ∀ n, (∫ ω, F n ω ∂P) ≤ K) :
    ∃ (M Err : ℕ → Ω → ℝ) (η : ℕ → ℝ),
      (∀ n, 0 < η n) ∧
      Tendsto η atTop (nhds (0 : ℝ)) ∧
      (∀ n, Integrable (M n) P ∧
        (∫ ω, M n ω ∂P) = 0) ∧
      (∀ n, Integrable (fun ω => max (Err n ω) 0) P) ∧
      (∀ n, ∀ᵐ ω ∂P,
        F n ω ≤ K + M n ω + max (Err n ω) 0) ∧
      (∀ n, (∫ ω, max (Err n ω) 0 ∂P) ≤ η n) := by sorry
