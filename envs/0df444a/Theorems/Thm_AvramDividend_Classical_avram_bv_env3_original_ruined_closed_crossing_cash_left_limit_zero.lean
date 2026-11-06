-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_env3_original_ruined_closed_crossing_cash_left_limit_zero
-- name    : AvramDividend.Classical.avram_bv_env3_original_ruined_closed_crossing_cash_left_limit_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:09:29.037857+00:00
-- url     : https://prove2.me/theorems/7e22a3b8-cbdf-4be5-ad87-d5f8eaafbd66
-- title:
--   Original ruined-clock closed cash has zero full left-neighbourhood limit at a positive horizon
-- statement:
--   For any original dividend strategy, when the payment clock has stopped by T>0, discounted Stieltjes cash over (a,T] tends to zero as a approaches T from below in the full left neighbourhood, regardless of physical-grid parameterisation.
-- source:
--   Fully Proved original closed left-limit source 0a6ff798 and strategy-free original stopped horizon-atom-zero ae7d2d61; Avram, Palmowski and Pistorius (2007), Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_env3_original_ruined_closed_crossing_cash_left_limit_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0)
    (hT : 0 < T) (hσ : σ ≤ (T : ℝ≥0∞))
    (q : ℝ) (hq : 0 ≤ q) :
    Tendsto (fun a : ℝ =>
      ∫⁻ t in paymentTimes σ ∩ Ioc a (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      (nhdsWithin (T : ℝ) (Iio (T : ℝ))) (nhds 0) := by sorry
