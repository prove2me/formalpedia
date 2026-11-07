-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_nonL1_generator_two_error_strict_expectation_limit
-- name    : AvramDividend.Classical.avram_bv_strict10_nonL1_generator_two_error_strict_expectation_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:28:59.308642+00:00
-- url     : https://prove2.me/theorems/fa1adcba-9be0-46ef-9a08-903acec91430
-- title:
--   Original BV strict expected value bound from two positive vanishing errors with no signed generator L1
-- statement:
--   For the actual source budget pattern of a nonnegative payoff, a centred integrable martingale, a nonpositive generator of unknown integrability, and separately integrable positive cell and contact errors whose expectations vanish, derive payoff integrability and an eventual upper expectation bound by base plus any positive epsilon. This is a reusable strict-dividend limiting bridge.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict10_nonL1_generator_two_error_strict_expectation_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F M B ErrCell ErrContact : ℕ → Ω → ℝ) (base : ℝ)
    (hM : ∀ n, Integrable (M n) P)
    (hMzero : ∀ n, (∫ ω, M n ω ∂P) = 0)
    (hCell : ∀ n, Integrable (fun ω => max (ErrCell n ω) 0) P)
    (hContact : ∀ n, Integrable (fun ω => max (ErrContact n ω) 0) P)
    (hFmeas : ∀ n, AEStronglyMeasurable (F n) P)
    (hFnonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hBnonpos : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hBudget : ∀ n, ∀ᵐ ω ∂P,
      F n ω ≤ base + (M n ω + B n ω) +
        max (ErrCell n ω) 0 + max (ErrContact n ω) 0)
    (hCellZero : Tendsto
      (fun n => ∫ ω, max (ErrCell n ω) 0 ∂P) atTop (nhds (0 : ℝ)))
    (hContactZero : Tendsto
      (fun n => ∫ ω, max (ErrContact n ω) 0 ∂P) atTop (nhds (0 : ℝ))) :
    (∀ n, Integrable (F n) P) ∧
      (∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, (∫ ω, F n ω ∂P) ≤ base + ε) := by sorry
