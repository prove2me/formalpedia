-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_strict10_two_scale_signed_expected_upper
-- name    : AvramDividend.Classical.avram_bv_strict10_two_scale_signed_expected_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T08:25:36.387895+00:00
-- url     : https://prove2.me/theorems/0f3fd478-6ccc-453a-810b-0d6e65ec4476
-- title:
--   Two-scale original BV signed expected upper budget without assuming integrability of generator source
-- statement:
--   For nonnegative measurable BV stopped payoffs with a nonpositive generator source and centred two-index martingale increments, if the positive interior and contact errors can be made arbitrarily small in inner-grid expectation up to an outer error tending to zero, then every payoff is integrable and its eventual expectation is at most the initial value plus any positive slack.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_strict10_two_scale_signed_expected_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (F B : ℕ → Ω → ℝ)
    (M ErrCell ErrContact : ℕ → ℕ → Ω → ℝ)
    (η : ℕ → ℝ) (base : ℝ)
    (hM : ∀ n k, Integrable (M n k) P)
    (hMzero : ∀ n k, (∫ ω, M n k ω ∂P) = 0)
    (hCell : ∀ n k, Integrable (fun ω => max (ErrCell n k ω) 0) P)
    (hContact : ∀ n k, Integrable (fun ω => max (ErrContact n k ω) 0) P)
    (hFmeas : ∀ n, AEStronglyMeasurable (F n) P)
    (hFnonneg : ∀ n, ∀ᵐ ω ∂P, 0 ≤ F n ω)
    (hBnonpos : ∀ n, ∀ᵐ ω ∂P, B n ω ≤ 0)
    (hBudget : ∀ n k, ∀ᵐ ω ∂P,
      F n ω ≤ base + (M n k ω + B n ω) +
        max (ErrCell n k ω) 0 + max (ErrContact n k ω) 0)
    (hη : Tendsto η atTop (nhds (0 : ℝ)))
    (hErrors : ∀ n (ε : ℝ), 0 < ε →
      ∃ k : ℕ,
        (∫ ω, max (ErrCell n k ω) 0 ∂P) +
          (∫ ω, max (ErrContact n k ω) 0 ∂P) ≤ η n + ε) :
    (∀ n, Integrable (F n) P) ∧
      (∀ ε : ℝ, 0 < ε →
        ∀ᶠ n in atTop, (∫ ω, F n ω ∂P) ≤ base + ε) := by sorry
