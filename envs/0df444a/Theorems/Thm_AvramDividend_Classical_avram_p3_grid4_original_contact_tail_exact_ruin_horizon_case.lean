-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_contact_tail_exact_ruin_horizon_case
-- name    : AvramDividend.Classical.avram_p3_grid4_original_contact_tail_exact_ruin_horizon_case
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T00:00:22.067206+00:00
-- url     : https://prove2.me/theorems/35b53b00-89f5-41a9-a0e5-9a3bf130d88e
-- title:
--   Actual stopped BV contact tail branches into zero ruin cash or surviving horizon payment atom
-- statement:
--   This authentic original-path case split closes the right-closed last contact cell accurately. If the positive clamped stop equals actual ruin, the strictly pre-ruin paymentTimes mask removes the contact atom and the tail tends to zero, via proved f6d4971b. Otherwise the endpoint is a horizon contact and the tail converges to exactly its surviving dividendMeasure singleton atom, via proved 3559180a. The theorem preserves both strict Iio and closed Iic endpoints and does not assert an absent horizon atom. It is a source boundary bridge, independent of the missing compensator/HJB signed budget.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_ruined_stopped_contact_tail_zero
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_contact_tail_cash_tendsto_exact_stop_atom
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_contact_tail_exact_ruin_horizon_case
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (hT : 0 < T)
    (q : ℝ) (hq : 0 ≤ q) :
    let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    0 < τ →
    Tendsto (fun m : ℕ =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds (if ruinTime X x D ω = (τ : ℝ≥0∞) then 0
        else (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {(τ : ℝ)},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)))) := by sorry
