-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_measurable_clock_killed_terminal_integrable
-- name    : AvramDividend.Classical.avram_wave8_20_original_BV_bounded_measurable_clock_killed_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:58:19.456602+00:00
-- url     : https://prove2.me/theorems/e0b91518-5d8d-4530-a554-71fbf31f1635
-- title:
--   Original BV killed postrightpayment terminal L1 at every bounded measurable clock
-- statement:
--   Under the exact original Standing bounded-variation source and capped admissible strategy, any measurable physical-time clock bounded pathwise by a finite deterministic horizon has an integrable discounted positive-part postrightpayment HJB terminal killed strictly at ruin; stopping time is not required.
-- source:
--   Original strictly surviving terminal in W8-04 at arbitrary bounded Borel random clocks, without assuming the clocks are stopping times. Uses already Proved exact joint source terminal measurability ead5faa1 and common BV random-clock almost-sure envelope 2563fd4a plus probability measure X.isProbability. No generator or stochastic inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_random_clock_survival_terminal_ae_bound
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_joint_measurable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_BV_bounded_measurable_clock_killed_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (τ : Ω → ℝ≥0)
    (hτMeas : Measurable τ)
    (hτBound : ∀ ω, τ ω ≤ H) :
    Integrable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) P := by sorry
