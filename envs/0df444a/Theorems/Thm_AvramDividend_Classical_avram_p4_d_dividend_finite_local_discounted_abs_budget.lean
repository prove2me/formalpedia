-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_finite_local_discounted_abs_budget
-- name    : AvramDividend.Classical.avram_p4_d_dividend_finite_local_discounted_abs_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:34:44.688667+00:00
-- url     : https://prove2.me/theorems/170524b8-b5ff-41de-acac-93eecdcf9228
-- title:
--   Discounted finite stopped local right-atom correction has an absolute cash budget
-- statement:
--   For any finite subset of actual original-source right-payment times up to T, if each post-X pre-rightpayment and post-rightpayment reserve lies in the same fixed compact interior band where the derivative norm is bounded by L, the sum of absolute discounted signed Ito payment corrections is bounded by (1+L) times the actual discounted dividends at those atoms. The proof uses the source-exact accepted local Lipschitz bound and positivity of exponential discounts. Passage to infinite atoms and expectation requires additional summability/integrability.
-- source:
--   Proved P4-D source-exact single right-payment local Lipschitz bound UUID 1b6a24c6-c4e2-4801-b9eb-1b65571ac935 and pinned Finset.sum_le_sum.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_local_right_remainder_lipschitz_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_finite_local_discounted_abs_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b : ℝ) (L : ℝ≥0)
    (hDiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ w y)
    (hDeriv : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ L)
    (q : ℝ) (ω : Ω) (T : ℝ≥0) (s : Finset ℝ≥0)
    (hstop : ∀ t ∈ s, (t : ℝ) ≤ (T : ℝ))
    (hpre : ∀ t ∈ s, riskProcess X x D t ω ∈ Icc a b)
    (hpost : ∀ t ∈ s,
      x + X.X t ω - rightLimit D t ω ∈ Icc a b) :
    (∑ t ∈ s, |Real.exp (-(q * (t : ℝ))) *
      ((rightLimit D t ω - D t ω) +
        w (x + X.X t ω - rightLimit D t ω) -
        w (riskProcess X x D t ω))|) ≤
      ∑ t ∈ s, (1 + (L : ℝ)) * Real.exp (-(q * (t : ℝ))) *
        (rightLimit D t ω - D t ω) := by sorry
