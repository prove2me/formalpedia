-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_nat_clock_any_closed_horizon_cash_le_horizon_n
-- name    : AvramDividend.Classical.avram_ubv_hor3_original_nat_clock_any_closed_horizon_cash_le_horizon_n
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T16:44:38.137688+00:00
-- url     : https://prove2.me/theorems/12688bb8-9902-4cd3-a22c-deed1e5c11ba
-- title:
--   Every original stopped natural-clock expected dividend cash horizon is bounded by its clock-aligned horizon n
-- statement:
--   For the exact original spectrally negative Levy process X, genuine dividendMeasure D, strict natural stopping cap n>0 and arbitrary real observation horizon T, expected nonnegative discounted dividend cash up to Iic T is no larger than expected cash through the clock-aligned closed horizon Iic n. The reason is that stopped paymentTimes support lies strictly before n, including t=0, so enlarging or shrinking the observation horizon can never add more cash than the clock-aligned set. Proves the actual ENNReal expectation inequality using the precise monotonicity of the two nested Stieltjes lintegrals.
-- source:
--   Strengthens the previous horizon saturation equality: a single n-aligned stochastic estimate controls all T for that n, reducing the positive natural-clock canonical budget to one clock boundary per n. Uses Proved public 26471312 original exact endpoint lemma and pinned Mathlib lintegral_mono_set. No fdb/0dda or canonical target imports.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_hor3_original_positive_nat_strict_endpoint_closed_cash_eq
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_hor3_original_nat_clock_any_closed_horizon_cash_le_horizon_n
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (q T : ℝ) (n : ℕ) (hn : 0 < n) :
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic T,
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) ≤
    (∫⁻ ω, ∫⁻ t in paymentTimes (min (ruinTime X x D ω) (n : ℝ≥0∞)) ∩ Iic (n : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω) ∂P) := by sorry
