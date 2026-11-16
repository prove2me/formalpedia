-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_nojump_tenth_clipped_cash_plus_terminal_lower
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_nojump_tenth_clipped_cash_plus_terminal_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:38:06.569222+00:00
-- url     : https://prove2.me/theorems/7382e237-034c-45ed-a845-4a64a1831dd5
-- title:
--   Original zero-barrier nojump physical clipped discounted cash plus survival terminal exceeds its fixed positive lower bound
-- statement:
--   At T=1/10 on every genuine unit-drift linear nojump original source path through time one, for all physical grid indices n≥4, the exact original strictly ruin-stopped discounted real Stieltjes dividend cash and actual half-unit affine survival terminal total at least (2/25+1/2)exp(−1/10). This is the core source-exact lower bound for disproof of the drift-only BV physical-error claim.
-- source:
--   Use Proved original zero-barrier admissible dividends, strict-time survival, linear path Stieltjes mass on (0,2/25], inclusion in paymentTimes∩Iio(T−δ_n), finite integral and real cash lower bound, and exact zero reserve at T. No altered stopping clock, dividend measure, or source process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_nojump_tenth_clipped_cash_plus_terminal_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (hDrift : X.drift = 1)
    (hPath : ∀ t : ℝ≥0, t ≤ (1 : ℝ≥0) →
      X.X t ω = (t : ℝ) * X.drift)
    (n : ℕ) (hn : 4 ≤ n) :
    let D := barrierStrategy X 0 0
    let T : ℝ := 1 / 10
    let w : ℝ → ℝ := fun y => if y < 0 then 0 else 1 / 2 + y
    (2 / 25 + 1 / 2 : ℝ) * Real.exp (-T) ≤
      (∫⁻ t in paymentTimes (ruinTime X 0 D ω) ∩
          Iio (T - T / ((n : ℝ) + 2)),
        ENNReal.ofReal (Real.exp (-t)) ∂(dividendMeasure D ω)).toReal +
        (if ((1 / 10 : ℝ≥0) : ℝ≥0∞) <
           ruinTime X 0 D ω then
          Real.exp (-T) * w (riskProcess X 0 D (1 / 10 : ℝ≥0) ω)
         else 0) := by sorry
