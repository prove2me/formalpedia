-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_cap_start_zero_grid_blocks_strict_band_cofinality
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_cap_start_zero_grid_blocks_strict_band_cofinality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T21:41:53.862735+00:00
-- url     : https://prove2.me/theorems/682fb7d9-446d-47a3-9b43-7cf035d414ec
-- title:
--   Original cap-start at observed zero defeats strict interior exit-clock prefix coverage
-- statement:
--   At a genuine original capped-control starting capital x=c with no time-zero right payout, any observation grid containing physical time zero samples the postpayment reserve at exactly the cap. Every strict subcap upper band excludes that sample, so the finite-prefix interior-cover premise needed for cofinal grid-exit localisation is false. A source-backed conditional obstruction, not an assertion about general sample paths.
-- source:
--   Original SpectrallyNegativeLevy.X_zero, DividendStrategy.rightLimit/IsAdmissibleLe and Proved Wave7-18 prefix-cover criterion 8c9b05d2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A zero-time observation of an unpaid cap-start invalidates strict interior prefix coverage. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_cap_start_zero_grid_blocks_strict_band_cofinality
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (c x : ℝ) (hc : 0 < c) (hxc : x = c)
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (ω : Ω) (hNoInitialPayment : rightLimit D 0 ω = 0)
    (r : ℕ → ℝ≥0) (hr0 : r 0 = 0)
    (lower upper : ℕ → ℝ) (hUpper : ∀ n, upper n < c) :
    ¬ (∀ m : ℕ, ∃ n : ℕ, m < n ∧
      ∀ k ≤ m, lower n ≤ x + X.X (r k) ω - rightLimit D (r k) ω ∧
        x + X.X (r k) ω - rightLimit D (r k) ω ≤ upper n) := by sorry
