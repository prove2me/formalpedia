-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_measurable_at_measurable_clock
-- name    : AvramDividend.Classical.avram_wave8_20_original_strict_survival_terminal_measurable_at_measurable_clock
-- status  : Open
-- author  : @WillR
-- created : 2026-11-02T21:12:59.886892+00:00
-- url     : https://prove2.me/theorems/5f695a4f-6e10-4f05-8ffd-f5253cd0c4b1
-- title:
--   Original strictly killed postrightpayment HJB payoff measurable at every measurable physical random clock
-- statement:
--   For every measurable physical-time random clock on the source Ω, the exact strictly killed postrightpayment discounted positive-part candidate terminal is measurable. This isolates the measurability input to dominated integrability and stopping estimates independently of BV drift and stochastic inequality.
-- source:
--   Faithful original controlled terminal with exact ruinTime, source rightLimit D and full physical-time domain. Direct specialization of accepted W8-20 joint source measurable theorem ead5faa1 along Measurable clock paired with identity, using pinned Measurable.prodMk. A boundedness, stopping time, or supermartingale hypothesis is unnecessary for measurability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_terminal_joint_measurable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_strict_survival_terminal_measurable_at_measurable_clock
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0) (q : ℝ)
    (τ : Ω → ℝ≥0) (hτ : Measurable τ) :
    Measurable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) := by sorry
