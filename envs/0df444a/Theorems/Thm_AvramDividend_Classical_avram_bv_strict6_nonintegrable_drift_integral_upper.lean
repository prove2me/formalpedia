-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict6_nonintegrable_drift_integral_upper
-- name    : AvramDividend.Classical.avram_bv_strict6_nonintegrable_drift_integral_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T12:17:33.102361+00:00
-- url     : https://prove2.me/theorems/6dd82b38-3f70-4b91-a141-ffd2b9b425c2
-- title:
--   Drop original nonpositive signed drift before expected-budget integration without its L1 hypothesis
-- statement:
--   A general positive-error expectation bridge for the original BV strict physical-grid payoff once its exact source-identification hypotheses are supplied. If finite-grid payoff F, centred stopped original compensated source M, and positive source-error E have L1 control, while authentic HJB/raw-negative-jump residual B is only almost surely nonpositive, then each expected payoff is at most the benchmark plus expected positive error. No Integrable B hypothesis is needed. This genuine measure-theoretic source step can later be instantiated with the exact original X,D grid and already-Proved residual sign, avoiding the full-clock generator L1 branch.

import Mathlib
open MeasureTheory
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict6_nonintegrable_drift_integral_upper
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P]
    (a : ℝ) (F M B E : ℕ → Ω → ℝ)
    (hF : ∀ n, Integrable (F n) P)
    (hM : ∀ n, Integrable (M n) P ∧ (∫ ω, M n ω ∂P) = 0)
    (hE : ∀ n, Integrable (fun ω => max (E n ω) 0) P)
    (hB : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hPath : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ a + M n ω + B n ω + max (E n ω) 0) :
    ∀ n, (∫ ω, F n ω ∂P) ≤
      a + (∫ ω, max (E n ω) 0 ∂P) := by sorry
