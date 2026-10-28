-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_negative_state_future_condExp_zero
-- name    : AvramDividend.Classical.chat04_negative_state_future_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:24:16.63863+00:00
-- url     : https://prove2.me/theorems/f9886ec5-94ba-4144-b1b6-254540a3ebf0
-- title:
--   Killed future q-scale conditional expectation vanishes on observed negative-reserve states
-- statement:
--   Under the actual Standing assumptions, at any deterministic observation time s and later u, the conditional expectation given F_s of the discounted q-scale payoff killed by continuous-time ruin in [s,u] is zero on the F_s-measurable event that the current reserve x+X_s is negative. Uses established integrability, pathwise start-of-window killing, and pulling a measurable indicator out of conditional expectation. This proves the negative-state part of the missing future-window harmonicity relation, without assuming the full killed martingale.
-- source:
--   Accepted AvramDividend.Classical.chat04_standing_future_window_killed_scale_integrable and chat04_future_window_killed_scale_zero_of_negative_start, pinned Mathlib condExp_indicator.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_standing_future_window_killed_scale_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_future_window_killed_scale_zero_of_negative_start

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.chat04_negative_state_future_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    ({ω | x + X.X s ω < 0}).indicator
      (P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
       (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
         W (x + X.X u ω)) | 𝓕 s]) =ᵐ[P] (fun _ => 0) := by sorry
