-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_capped_ruin_clock_terminal_integrable
-- name    : AvramDividend.Classical.avram_wave8_20_original_BV_capped_ruin_clock_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:32:58.588645+00:00
-- url     : https://prove2.me/theorems/9c1faaa0-1c3f-4302-97ed-1f3da52a20ed
-- title:
--   Genuine finite capped-ruin stopping clocks yield integrable original killed BV terminal
-- statement:
--   For each natural finite horizon, convert the canonical original bounded ruin clock min(ruinTime,n) into a physical nonnegative time and show the exact strictly killed postrightpayment BV candidate terminal is integrable at this true stopped clock.
-- source:
--   The source strict ruinTime min deterministic n is already a real stopping time in 𝓕.rightCont by Proved f5caff4b. Convert this finite ENNReal stopped time into NNReal physical clock via toNNReal and prove exact coe equality using finite upper bound; then apply accepted b438eaf6 BV terminal L1 at bounded genuine rightcontinuous stopping clock. No supermartingale estimate used.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_ubv_original_deterministic_bounded_ruin_stopping_package
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_random_stop_survival_terminal_integrable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_BV_capped_ruin_clock_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal
    Integrable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) P := by sorry
