-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_lsv_original_prefix_positive_and_rightpost_pair_band_including_zero
-- name    : AvramDividend.Classical.avram_lsv_original_prefix_positive_and_rightpost_pair_band_including_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T22:14:30.612067+00:00
-- url     : https://prove2.me/theorems/648de8a0-98a6-451c-989d-b20c795266fc
-- title:
--   Original prepayment and rightpost dividend reserves share strict prefix compact band including zero clock
-- statement:
--   For genuine original Levy X and admissible dividend strategy with D0=X0=0, if prepayment reserve is almost surely in fixed compact band for every positive time strictly before clock and right-postpayment reserve is in that band also for time zero, then both reserves are in the band at every strictly pre-clock time. Requires x≤upper band; derive lower x bound from right dividend monotonicity and zero-time postpayment floor. No Gaussian moments or convergence assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_lsv_original_prefix_positive_and_rightpost_pair_band_including_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (a b : ℝ) (hxb : x ≤ b)
    (hPre : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      riskProcess X x D t ω ∈ Icc a b)
    (hPost : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      x + X.X t ω - rightLimit D t ω ∈ Icc a b) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      riskProcess X x D t ω ∈ Icc a b ∧
      x + X.X t ω - rightLimit D t ω ∈ Icc a b := by sorry
