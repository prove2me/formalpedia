-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_actual_stopped_positive_ruin_dividend_mass_cumulative
-- name    : AvramDividend.Classical.avram_wave4_03_actual_stopped_positive_ruin_dividend_mass_cumulative
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T10:45:45.594053+00:00
-- url     : https://prove2.me/theorems/2c290315-394a-4301-8573-a0efbce26af9
-- title:
--   Exact positive finite-ruin full Stieltjes dividend mass equals pre-ruin cumulative payments
-- statement:
--   For any genuine left-continuous admissible-form dividend strategy and strictly positive finite stopping horizon tau, the entire actual Lebesgue–Stieltjes dividend measure of original paymentTimes tau, restricted through tau, is exactly ENNReal.ofReal(D tau). This counts diffuse and singular-continuous payments and the initial time-zero atom, while excluding right-payment atoms at the ruin time. This is an endpoint accounting identity and does not establish source Lévy jump compensation or the stochastic HJB bound.
-- source:
--   Canonical paymentTimes_eq_strict_of_pos 7c01995b-bd0b-43b0-bb5e-3a05fb37de5b, dividendMeasure_Ico_zero_eq_dividendValue 56472398-9e4f-43ea-9dc2-772f94a501cf, Avram–Palmowski–Pistorius (2007), Proposition 4(i).

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_paymentTimes_eq_strict_of_pos
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave4_03_actual_stopped_positive_ruin_dividend_mass_cumulative
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (τ : ℝ≥0) (hτ : 0 < τ) :
    dividendMeasure D ω
      (paymentTimes (τ : ℝ≥0∞) ∩ Set.Iic (τ : ℝ)) =
      ENNReal.ofReal (D τ ω) := by sorry
