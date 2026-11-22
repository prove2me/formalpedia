-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_original_stop_cash_exact_closed_or_halfopen_endpoint
-- name    : AvramDividend.Classical.avram_jump6_original_stop_cash_exact_closed_or_halfopen_endpoint
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T19:02:58.509076+00:00
-- url     : https://prove2.me/theorems/765f5efc-c752-4ff5-b473-fa1e56fb87db
-- title:
--   Original ruin-clipped cash support has exact closed pre-ruin versus half-open ruin-contact endpoint
-- statement:
--   For an original spectrally negative Lévy-controlled reserve and any physical stopping clock τ no later than the actual ruin time, identify the canonical paymentTimes(ruin)∩Iic(τ) exactly: the interval [0,τ] if τ=0 or τ is strictly pre-ruin; the interval [0,τ) if the positive stopped clock contacts ruin. This is the exact dividend-payment endpoint convention required for the original stopped Itô–Meyer reward ledger, including the initial payment atom and exclusion of payments at ruin. The proof combines existing Proved pre-ruin and ruin-contact interval identities after proving the exhaustive endpoint dichotomy from τ≤ruin. It does not require Lévy jump moment assumptions or stochastic calculus.
-- source:
--   Avram Dividend Classical original stopped cash of finite-activity expected budget 15815eff-2c54-41e3-97a6-d216a3efb8d8 and infinite-activity 464200c8-be79-47cd-8938-79343e0d7fce; Proved identities bfe4a214-2dc7-40dc-b43d-19316d917a2e and 53e354b4-74f9-45a9-8afe-1535106d9f5d.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_06_original_zero_or_strict_preruin_random_clock_paymentTimes_eq_Icc
import Theorems.Thm_AvramDividend_Classical_avram_wave8_21_original_ruin_horizon_paymentTimes_eq_Ico
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_original_stop_cash_exact_closed_or_halfopen_endpoint
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (ω : Ω) (τ : Ω → ℝ≥0)
    (hRuinBound : (τ ω : ℝ≥0∞) ≤ ruinTime X x D ω) :
    paymentTimes (ruinTime X x D ω) ∩ Iic (τ ω : ℝ) =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then Icc (0 : ℝ) (τ ω : ℝ)
      else Ico (0 : ℝ) (τ ω : ℝ) := by sorry
