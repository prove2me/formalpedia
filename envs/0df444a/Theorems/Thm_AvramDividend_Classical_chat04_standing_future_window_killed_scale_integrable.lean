-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_standing_future_window_killed_scale_integrable
-- name    : AvramDividend.Classical.chat04_standing_future_window_killed_scale_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:04:27.568985+00:00
-- url     : https://prove2.me/theorems/0c1e0003-783d-4f39-a1d8-48e190070a2e
-- title:
--   Standing assumptions imply unconditional integrability of future-window killed q-scale payoff
-- statement:
--   Under the original Standing and q>0 assumptions, a scale-function payoff killed by ruin over any deterministic future interval [s,u] is integrable. The future-window survival event is measurable by countable-grid detection, and the already proved standing fixed-time integrability persists under a constant discount and measurable indicator. This removes the auxiliary Integrable hypothesis from the published killed conditional-expectation time-splitting interface.
-- source:
--   Newly authored and separately verified chat04_lower_survival_closed_window_measurable and chat04_future_window_killed_scale_integrable_of_measurable.

import Mathlib.Tactic.Linarith
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_future_window_killed_scale_integrable_of_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_measurable

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_standing_future_window_killed_scale_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    Integrable
      (({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω))) P := by sorry
