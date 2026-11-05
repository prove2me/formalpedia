-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_local_cash_summable_implies_right_remainder_summable
-- name    : AvramDividend.Classical.avram_p4_d_dividend_local_cash_summable_implies_right_remainder_summable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:16:39.610196+00:00
-- url     : https://prove2.me/theorems/8b93c657-627b-40e3-8006-ff35f8df588b
-- title:
--   Original local right-dividend residual is absolutely summable whenever its stopped discounted cash envelope is summable
-- statement:
--   For the original Lévy path and dividend control, on any collection of actual right payment times whose pre-X-processed and post-right-payment reserves stay in a common compact interior derivative band, summability of discounted dividends times the local derivative coefficient forces absolute summability of the exact signed right-payment correction. This strengthens the finite budget lemma and discharges the summability assumption in the accepted P4-D right-atom tsum sign lemma under a genuine cash summability premise. No global boundary or L1 assumption is invented.
-- source:
--   Original riskProcess/rightLimit; accepted single-atom local cash Lipschitz UUID 1b6a24c6-c4e2-4801-b9eb-1b65571ac935; pinned Mathlib Summable.of_norm_bounded (Mathlib.Analysis.Normed.Group.InfiniteSum).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_local_right_remainder_lipschitz_bound
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_local_cash_summable_implies_right_remainder_summable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b : ℝ) (L : ℝ≥0)
    (hDiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ w y)
    (hDeriv : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ L)
    (ω : Ω) (q : ℝ) (A : Set ℝ≥0)
    (hpre : ∀ t : A, riskProcess X x D (t : ℝ≥0) ω ∈ Icc a b)
    (hpost : ∀ t : A,
      x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω ∈ Icc a b)
    (hcash : Summable (fun t : A =>
      Real.exp (-(q * (((t : ℝ≥0) : ℝ)))) *
        ((1 + (L : ℝ)) *
          (rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω)))) :
    Summable (fun t : A =>
      Real.exp (-(q * (((t : ℝ≥0) : ℝ)))) *
        ((rightLimit D (t : ℝ≥0) ω - D (t : ℝ≥0) ω) +
          w (x + X.X (t : ℝ≥0) ω - rightLimit D (t : ℝ≥0) ω) -
          w (riskProcess X x D (t : ℝ≥0) ω))) := by sorry
