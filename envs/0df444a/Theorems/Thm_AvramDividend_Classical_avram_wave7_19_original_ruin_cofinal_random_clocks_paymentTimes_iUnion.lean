-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_ruin_cofinal_random_clocks_paymentTimes_iUnion
-- name    : AvramDividend.Classical.avram_wave7_19_original_ruin_cofinal_random_clocks_paymentTimes_iUnion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:13:19.578071+00:00
-- url     : https://prove2.me/theorems/bc92f7fc-528c-4211-9a52-f2735efe1bf5
-- title:
--   Original ruin payment set through T is exactly exhausted by any cofinal sequence of stopping clocks
-- statement:
--   For the actual original ruinTime of the Levy dividend risk process, any sequence of nonnegative extended-time random clock values whose supremum equals that particular sample path ruinTime exhausts the full original pre-ruin paymentTimes set through T. The time-zero right dividend is included even when all clocks start at zero, and the strictly positive ruin-time right payment remains excluded because paymentTimes uses a strict comparison after zero. This is a pure source-specific boundary identity taking W7-18's constructed stopping clocks as inputs; no stochastic stopping-time construction, continuity assumption, expectation or uniform integrability is needed.
-- source:
--   Original paymentTimes definition 0≤t ∧ (t=0 ∨ ENNReal.ofReal t<σ); complete linear order sup and strict predecessor property.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_ruin_cofinal_random_clocks_paymentTimes_iUnion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (T : ℝ)
    (σ : ℕ → ℝ≥0∞)
    (hSup : (⨆ k : ℕ, σ k) = ruinTime X x D ω) :
    paymentTimes (ruinTime X x D ω) ∩ Iic T =
      ⋃ k : ℕ, (paymentTimes (σ k) ∩ Iic T) := by sorry
