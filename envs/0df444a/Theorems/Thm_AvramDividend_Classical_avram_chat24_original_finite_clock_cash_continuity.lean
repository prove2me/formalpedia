-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_original_finite_clock_cash_continuity
-- name    : AvramDividend.Classical.avram_chat24_original_finite_clock_cash_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:53:44.600512+00:00
-- url     : https://prove2.me/theorems/804e8041-fd01-4b33-ba9e-595ce7c0207b
-- title:
--   AvramDividend.Classical.avram_chat24_original_finite_clock_cash_continuity
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_original_finite_clock_cash_continuity from oversized parent candidate d940b6b78cf8895596030f7a6e5efb70bf08f07efbd59c5c976fb89689230046.
-- source:
--   candidate-decomposition:fcea3ff9-d1d8-4e51-a67b-ca75c8c222e9:d940b6b78cf8895596030f7a6e5efb70bf08f07efbd59c5c976fb89689230046

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_true_stopped_discount_integrableOn_dividendMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem AvramDividend.Classical.avram_chat24_original_finite_clock_cash_continuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (t T : ℝ≥0) (ht : 0 < t) (htT : t ≤ T)
    (u : ℕ → ℝ≥0) (hu : ∀ n, u n < t) (hm : Monotone u)
    (hl : Tendsto u atTop (nhds t)) :
    Tendsto (fun n => (∫⁻ y in Ico (0 : ℝ) (u n : ℝ),
        ENNReal.ofReal (Real.exp (-(q * y))) ∂(dividendMeasure D ω)).toReal) atTop
      (nhds (∫⁻ y in paymentTimes (t : ℝ≥0∞) ∩ Iio (T : ℝ),
        ENNReal.ofReal (Real.exp (-(q * y))) ∂(dividendMeasure D ω)).toReal) := by sorry
end
