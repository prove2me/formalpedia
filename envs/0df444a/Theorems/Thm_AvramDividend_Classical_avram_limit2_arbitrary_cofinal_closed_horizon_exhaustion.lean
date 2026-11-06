-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_arbitrary_cofinal_closed_horizon_exhaustion
-- name    : AvramDividend.Classical.avram_limit2_arbitrary_cofinal_closed_horizon_exhaustion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T11:56:45.454231+00:00
-- url     : https://prove2.me/theorems/3e54faf4-b686-48d3-952a-9f9a80de3f6c
-- title:
--   Exact genuine original perpetual dividend value along arbitrary cofinal deterministic closed real horizons
-- statement:
--   Every cofinal deterministic family T:ℕ→ℝ, without needing monotonicity or positivity, exhausts original dividendValue through actual discounted Stieltjes payout on paymentTimes(ruinTime) intersect Iic(T k). Integer horizon truncation is the accepted source theorem. Every integer horizon is contained in some cofinal T(k), and every finite T(k) is contained in an integer ceiling. Monotone set and outer lintegrals sandwich the two suprema. All finite right-boundary and time-zero atoms remain included without terminal assumptions or equality in law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendValue_eq_iSup_truncated

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_arbitrary_cofinal_closed_horizon_exhaustion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissible X x D)
    (T : ℕ → ℝ) (hT : ∀ a : ℝ, ∃ k : ℕ, a ≤ T k) :
    dividendValue X q x D =
      ⨆ k : ℕ,
        ∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (T k),
          ENNReal.ofReal (Real.exp (-(q * t)))
            ∂(dividendMeasure D ω) ∂P := by sorry
