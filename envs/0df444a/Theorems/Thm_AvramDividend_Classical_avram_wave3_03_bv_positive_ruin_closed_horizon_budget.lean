-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_positive_ruin_closed_horizon_budget
-- name    : AvramDividend.Classical.avram_wave3_03_bv_positive_ruin_closed_horizon_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T12:19:27.041128+00:00
-- url     : https://prove2.me/theorems/1ac6c9a4-0290-4384-ad0e-5c96945c947c
-- title:
--   BV original complete closed-horizon dividend Stieltjes reward bound on positive-ruin paths
-- statement:
--   For an actual bounded-variation spectrally negative Levy dividend process whose ruin time is positive, the complete stopped dividend Stieltjes integral through a deterministic terminal horizon T, including the terminal payment atom, is bounded almost surely by initial reserve plus H times physical drift for any H strictly later than T. Includes paths ruined before T, as well as continuously paid dividends.
-- source:
--   Original Lévy positive-ruin stopped drift bound; exact inclusion of the canonical paymentTimes ruin set restricted to Iic T into paymentTimes (min ruin H) when T < H.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_positive_ruin_strict_stopped_drift_budget

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave3_03_bv_positive_ruin_closed_horizon_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (q : ℝ) (hq : 0 ≤ q) (T H : ℝ≥0) (hTH : T < H) :
    ∀ᵐ ω ∂P, 0 < ruinTime X x D ω →
      (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * t)))
          ∂(dividendMeasure D ω)) ≤
        ENNReal.ofReal (x + (H : ℝ) * X.drift) := by sorry
