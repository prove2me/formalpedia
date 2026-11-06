-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_contact_tail_cash_tendsto_exact_stop_atom
-- name    : AvramDividend.Classical.avram_p3_grid4_original_contact_tail_cash_tendsto_exact_stop_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:08:53.58337+00:00
-- url     : https://prove2.me/theorems/3559180a-5823-496b-bf6a-102ef13b4ccb
-- title:
--   Original X/D stopped shrinking contact-tail cash converges exactly to retained stop atom
-- statement:
--   For the genuine original spectrally negative Levy X and original strategy D, at any positive ruin/horizon-clamped clock tau, the discounted dividendMeasure cash in the shrinking right-closed paymentTimes tail Ioc(tau-T/(m+1),tau) converges in ENNReal to the exact stopped singleton payment atom at tau. This source-faithful limit composes the newly proved grid4 positive-endpoint approach certificate with the independently proved BV-ENV3 right-closed crossing-cell limit 7a479ca3. On positive ruin, the singleton is absent from paymentTimes; at a surviving T, its right-payment mass remains. The tau=0 branch is separate.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_contact_left_endpoint_approach_certificate
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_closed_crossing_cell_cash_tendsto_horizon_atom
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_contact_tail_cash_tendsto_exact_stop_atom
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
      atTop (nhds
        (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ {(τ : ℝ)},
          ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
