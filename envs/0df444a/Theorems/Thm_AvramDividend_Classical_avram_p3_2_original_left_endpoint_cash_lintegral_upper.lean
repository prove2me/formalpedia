-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_left_endpoint_cash_lintegral_upper
-- name    : AvramDividend.Classical.avram_p3_2_original_left_endpoint_cash_lintegral_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:16:27.264869+00:00
-- url     : https://prove2.me/theorems/5fc91158-69f1-443c-b996-acf4ffb894cc
-- title:
--   Original physical stopped Stieltjes discount bounded by left-endpoint cash
-- statement:
--   For each original stopped X/D cash cell, the exact once-discounted physical dividendMeasure integral is bounded above by the original paymentTimes-restricted mass weighted with exponential discount at the left cell endpoint.
-- source:
--   Use ae_restrict_mem in the Borel Ioc mesh cell, real exp monotonicity for q≥0, ENNReal.ofReal_le_ofReal, lintegral_mono_ae and lintegral_const_mul to obtain the source-exact ENNReal upper estimate.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_left_endpoint_cash_lintegral_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ≥0) (m i : ℕ) :
    let τ : ℝ≥0 :=
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    let u : ℕ → ℝ≥0 := fun j =>
      min (((min j (m + 1) : ℕ) : ℝ≥0) *
        (T / (m + 1))) τ
    let ν : Measure ℝ :=
      (dividendMeasure D ω).restrict (paymentTimes (ruinTime X x D ω))
    (∫⁻ t in Ioc (u i : ℝ) (u (i + 1) : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂ν) ≤
    ENNReal.ofReal (Real.exp (-(q * (u i : ℝ)))) *
      (∫⁻ t in Ioc (u i : ℝ) (u (i + 1) : ℝ),
        (1 : ℝ≥0∞) ∂ν):= by sorry
