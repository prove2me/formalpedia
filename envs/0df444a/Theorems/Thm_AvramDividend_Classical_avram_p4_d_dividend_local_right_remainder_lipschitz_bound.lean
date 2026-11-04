-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_local_right_remainder_lipschitz_bound
-- name    : AvramDividend.Classical.avram_p4_d_dividend_local_right_remainder_lipschitz_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:14:54.643513+00:00
-- url     : https://prove2.me/theorems/1b6a24c6-c4e2-4801-b9eb-1b65571ac935
-- title:
--   Source-exact right-dividend signed residual has a cash-dominated bound on any local derivative-controlled reserve band
-- statement:
--   For a genuine original monotone dividend strategy, if the post-X/pre-D and post-rightpayment reserves lie in a compact real interval where w is differentiable with derivative norm bounded by L, the absolute signed right-payment residual is at most (1+L) times the actual nonnegative dividend ΔD_t. This gives a stopped local L1 domination by discounted dividend cash once P4-F proves a uniform compact derivative bound and integrates/sums the exact right atoms. It does not falsely infer global derivative boundedness at zero/cap.
-- source:
--   Original riskProcess/rightLimit definitions, proved dividendStrategy_le_rightLimit and generic Wave8 compact derivative/Lipschitz theorem 596e81d8; arithmetic source identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_compact_derivative_implies_lipschitz
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_d_dividend_local_right_remainder_lipschitz_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b : ℝ) (L : ℝ≥0)
    (hDiff : ∀ y ∈ Icc a b, DifferentiableAt ℝ w y)
    (hDeriv : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ L)
    (ω : Ω) (t : ℝ≥0)
    (hpre : riskProcess X x D t ω ∈ Icc a b)
    (hpost : x + X.X t ω - rightLimit D t ω ∈ Icc a b) :
    |(rightLimit D t ω - D t ω) +
      w (x + X.X t ω - rightLimit D t ω) - w (riskProcess X x D t ω)| ≤
      (1 + (L : ℝ)) * (rightLimit D t ω - D t ω) := by sorry
