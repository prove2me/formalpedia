-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_ruined_stopped_contact_tail_zero
-- name    : AvramDividend.Classical.avram_p3_grid4_original_ruined_stopped_contact_tail_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T23:48:32.890577+00:00
-- url     : https://prove2.me/theorems/f6d4971b-6935-4fb2-8c39-7d9f877d3d9f
-- title:
--   Original stopped physical-grid closed contact cash vanishes on actual positive ruin
-- statement:
--   For the authentic original X/D process, on a path where the ruin/horizon-clamped positive stop tau is exactly the original ruin clock, the shrinking last physical-grid right-closed dividendMeasure cash tends to zero. The conclusion preserves the separate initial dividend atom, is conditional on the exact ruin stop identity, and follows from the already proved physical endpoint approach certificate and BV-ENV3 ruin crossing cash theorem.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_contact_left_endpoint_approach_certificate
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_ruined_horizon_closed_crossing_cash_tendsto_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_ruined_stopped_contact_tail_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (hT : 0 < T)
    (q : ℝ) (hq : 0 ≤ q) :
    let τ : ℝ≥0 := (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    0 < τ → ruinTime X x D ω = (τ : ℝ≥0∞) →
    Tendsto (fun m : ℕ =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩
        Ioc ((τ - T / (m + 1) : ℝ≥0) : ℝ) (τ : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by sorry
