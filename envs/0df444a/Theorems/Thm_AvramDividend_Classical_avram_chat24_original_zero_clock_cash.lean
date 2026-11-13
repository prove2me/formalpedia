-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_chat24_original_zero_clock_cash
-- name    : AvramDividend.Classical.avram_chat24_original_zero_clock_cash
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:13:57.68055+00:00
-- url     : https://prove2.me/theorems/b75955fc-6a0f-4ce8-bdef-b964dc62d714
-- title:
--   AvramDividend.Classical.avram_chat24_original_zero_clock_cash
-- statement:
--   Automatically extracted helper theorem AvramDividend.Classical.avram_chat24_original_zero_clock_cash from oversized parent candidate d6cf3531c246d9a1a82e3e4eb6811415688d59ae1624a9e146f0c763af9a2f12.
-- source:
--   candidate-decomposition:235cf812-5f12-4e32-b966-4b84acac62f3:d6cf3531c246d9a1a82e3e4eb6811415688d59ae1624a9e146f0c763af9a2f12

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section
theorem AvramDividend.Classical.avram_chat24_original_zero_clock_cash
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (q T : ℝ) (hT : 0 < T) :
    (∫⁻ t in paymentTimes 0 ∩ Iio T, ENNReal.ofReal (Real.exp (-(q * t)))
      ∂(dividendMeasure D ω)).toReal ≤ rightLimit D 0 ω := by sorry
end
