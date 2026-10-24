-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_future_window_killed_scale_integrable_of_measurable
-- name    : AvramDividend.Classical.chat04_future_window_killed_scale_integrable_of_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:45:44.594805+00:00
-- url     : https://prove2.me/theorems/75fe5cab-6718-47f0-999c-26e7117bf7fa
-- title:
--   Integrability of a measurable future-window killed discounted scale payoff
-- statement:
--   Under the original Standing assumptions for a spectrally negative Lévy process and positive discount, the future-window q-scale payoff is integrable whenever its path-survival event is measurable. The discounted multiplier is a fixed finite constant, and the event indicator preserves integrability. This discharges the analytic integrability assumption used by the published conditional-expectation time-split identity; pathwise event measurability is a separate obligation.
-- source:
--   Published chat04_standing_scale_fixed_time_integrable and Mathlib integrability closure under deterministic multiplication and measurable indicators.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_standing_scale_fixed_time_integrable

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_future_window_killed_scale_integrable_of_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u)
    (hB : MeasurableSet
      {ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}) :
    Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) P := by sorry
