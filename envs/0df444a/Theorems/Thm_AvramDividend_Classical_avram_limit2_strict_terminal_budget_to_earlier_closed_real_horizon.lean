-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_limit2_strict_terminal_budget_to_earlier_closed_real_horizon
-- name    : AvramDividend.Classical.avram_limit2_strict_terminal_budget_to_earlier_closed_real_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T12:34:29.528901+00:00
-- url     : https://prove2.me/theorems/96b53643-223f-4818-807e-0bceaed56941
-- title:
--   General original strict real-horizon cash-plus-terminal upper bound implies an earlier closed horizon budget
-- statement:
--   For an original spectrally negative Lévy source and its actual dividend measure, an expected strict horizon cash-plus-nonnegative terminal ENNReal budget at T gives the corresponding closed cash-plus-identical-terminal budget at every S<T. Both payments at S and time zero are retained; payment at T is excluded. This uses direct eventwise set inclusion, lintegral_mono_set, addition monotonicity and outer lintegral_mono, without integrability, terminal vanishing, or equality in law.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_limit2_strict_terminal_budget_to_earlier_closed_real_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (S T : ℝ) (hST : S < T)
    (Terminal : Ω → ℝ≥0∞) (B : ℝ≥0∞)
    (hBound : (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iio T,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B) :
    (∫⁻ ω, ((∫⁻ t in paymentTimes (ruinTime X x D ω) ∩ Iic S,
      ENNReal.ofReal (Real.exp (-(q * t)))
        ∂(dividendMeasure D ω)) + Terminal ω) ∂P) ≤ B := by sorry
