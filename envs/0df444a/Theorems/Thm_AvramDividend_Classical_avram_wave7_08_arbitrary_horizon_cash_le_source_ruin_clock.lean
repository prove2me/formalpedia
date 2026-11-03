-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_08_arbitrary_horizon_cash_le_source_ruin_clock
-- name    : AvramDividend.Classical.avram_wave7_08_arbitrary_horizon_cash_le_source_ruin_clock
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T14:07:48.999936+00:00
-- url     : https://prove2.me/theorems/0008854e-2453-44f0-93b6-595e17472faf
-- title:
--   Arbitrary finite-horizon source truncated cash bounded by original ruin-time Stieltjes cash at clock n
-- statement:
--   For the canonical original Lévy process and cumulative dividends, any truncated-clock expected discounted cash at any horizon T is bounded by the original ruin-domain cash stopped at positive n. The two source-exact monotonicity results first shorten arbitrary T to n and then enlarge the truncated payment domain to the actual pre-ruin payment domain.
-- source:
--   Composes W7-08 Proved positive-clock horizon theorem 7b9deff0 and new source-ruin Stieltjes comparison 0607e136. Direct bridge into the W6-06 original finite-clock expected budget.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_08_arbitrary_horizon_cash_le_source_ruin_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (hn : 0 < n) (T : ℝ) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
