-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_ruined_horizon_closed_crossing_cash_tendsto_zero
-- name    : AvramDividend.Classical.avram_bv_env3_original_ruined_horizon_closed_crossing_cash_tendsto_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:21:54.959742+00:00
-- url     : https://prove2.me/theorems/5a7cefb8-ff7d-4cd8-ad3d-6bb89f32829d
-- title:
--   Original stopped right-closed crossing-cell cash vanishes when ruin precedes the horizon
-- statement:
--   At a positive horizon that is at or after the original stopped payment clock, and for any monotone last-grid left endpoints approaching that horizon from strictly below, the full right-closed final crossing-cell discounted cash tends to zero. Uses two fully Proved exact original-process source theorems: the last-cell cash converges to its singleton T payment, and the stopped clock rules that singleton out on ruined paths.
-- source:
--   Proved BV-ENV3 original closed crossing-cell cash limit (7a479ca3) and original stopped-clock horizon payment atom zero (d654b5a9), with direct rewriting. Avram, Palmowski and Pistorius (2007), Proposition 4(i), equation (5.13), actual original dividendMeasure/paymentTimes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_ruined_horizon_closed_crossing_cash_tendsto_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (hT : 0 < T) (hσ : σ ≤ (T : ℝ≥0∞))
    (q : ℝ) (hq : 0 ≤ q)
    (a : ℕ → ℝ) (ha : Monotone a)
    (hlim : Tendsto a atTop (nhds (T : ℝ)))
    (hbelow : ∀ n, a n < (T : ℝ)) :
    Tendsto (fun n =>
      ∫⁻ t in paymentTimes σ ∩ Ioc (a n) (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop (nhds 0) := by sorry
