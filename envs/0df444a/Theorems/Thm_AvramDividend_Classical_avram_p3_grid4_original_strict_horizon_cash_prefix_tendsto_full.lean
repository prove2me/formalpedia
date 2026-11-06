-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_original_strict_horizon_cash_prefix_tendsto_full
-- name    : AvramDividend.Classical.avram_p3_grid4_original_strict_horizon_cash_prefix_tendsto_full
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T22:55:47.890146+00:00
-- url     : https://prove2.me/theorems/2c2e08a6-5699-4770-bfda-bf9411a24864
-- title:
--   Original strict stopped discounted cash increases to full Iio horizon without horizon atom
-- statement:
--   For the actual original spectrally negative Levy X, admissible original dividends D and stopped paymentTimes, discounted dividendMeasure cash over Iio(T-delta_n) increases to exactly the strict Iio T cash as positive antitone widths tend to zero. The union of original measurable prefixes is precisely paymentTimes(ruinTime X x D omega) intersect Iio T. Continuity from below of the genuine weighted Stieltjes measure yields convergence in ENNReal without imposing L1 or uniform-integrability assumptions. This retains the time-zero right payment eventually, excludes the right horizon atom, and requires no change to X, D, or P.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_original_strict_horizon_cash_prefix_tendsto_full
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x C D) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (T : ℝ) (hT : 0 < T)
    (δ : ℕ → ℝ) (hδpos : ∀ n, 0 < δ n)
    (hδanti : Antitone δ) (hδ : Tendsto δ atTop (𝓝 0)) :
    Tendsto (fun n : ℕ =>
      ∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio (T - δ n),
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))
      atTop
      (𝓝 (∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
        ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω))) := by sorry
