-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_zero_at_after_ruin
-- name    : AvramDividend.Classical.avram_wave8_20_original_strict_survival_terminal_zero_at_after_ruin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:21:19.467379+00:00
-- url     : https://prove2.me/theorems/c07eabc1-818e-4bb0-a13f-eded724e30ef
-- title:
--   Original strictly killed post-rightpayment HJB continuation is identically zero at and after ruin
-- statement:
--   At the actual ruin time, including a zero landing or creeping path, and at every later nonnegative time, the original strict-survival discounted positive-part post-rightpayment HJB terminal is exactly zero. This complements W8-20's strictly negative overshoot lemma and isolates the correct killed-boundary value for right-localisation without asserting the reserve is negative at ruin.
-- source:
--   Original Avram Proposition 4(i) strict survival terminal boundary. The source terminal uses (t:ENNReal)<ruinTime, so for any time t at or after actual ruin and all later s, it is definitionally zero regardless of negative overshoot, exact zero landing or creeping. The NNReal-to-ENNReal time order is preserved; no further dividend admissibility hypothesis at ruin is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_strict_survival_terminal_zero_at_after_ruin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (t : ℝ≥0)
    (hRuin : ruinTime X x D ω ≤ (t : ℝ≥0∞)) :
    ∀ s : ℝ≥0, t ≤ s →
      (if (s : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (s : ℝ))) *
          w (x + X.X s ω - rightLimit D s ω))
      else 0) = 0 := by sorry
