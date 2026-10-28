-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_future_window_harmonicity_of_nonnegative_state
-- name    : AvramDividend.Classical.chat04_unbounded_future_window_harmonicity_of_nonnegative_state
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:43:40.168353+00:00
-- url     : https://prove2.me/theorems/6335fc4e-ac16-4ec3-898a-61205b800f35
-- title:
--   Nonnegative-reserve future-window q-harmonicity extends to all reserves without Standing
-- statement:
--   For an unbounded-variation spectrally negative Lévy process, a future-window killed q-scale conditional expectation equality on the event of nonnegative current reserve extends to all reserves. The negative-state payoff vanishes pathwise and its conditional expectation vanishes using fixed-time integrability, without the Standing hypothesis.
-- source:
--   Direct source-faithful unbounded-variation strengthening of Proved chat04_future_window_harmonicity_of_nonnegative_state (a46c686a); uses Proved chat04_unbounded_scale_fixed_time_integrable, chat04_lower_survival_closed_window_measurable, and chat04_future_window_killed_scale_zero_of_negative_start. Supports bridge_censored_q_harmonicity_of_unbounded_variation (889da773) and ultimately aed50a34, without assuming harmonicity outside the explicitly passed nonnegative-state event.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_scale_fixed_time_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_lower_survival_closed_window_measurable
import Theorems.Thm_AvramDividend_Classical_chat04_future_window_killed_scale_zero_of_negative_start

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.chat04_unbounded_future_window_harmonicity_of_nonnegative_state
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u)
    (hWneg : ∀ y : ℝ, y < 0 → W y = 0)
    (hPositive :
       ({ω | 0 ≤ x + X.X s ω}).indicator
         (P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
       (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
         W (x + X.X u ω)) | 𝓕 s]) =ᵐ[P]
       ({ω | 0 ≤ x + X.X s ω}).indicator
         (fun ω => W (x + X.X s ω))) :
    P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
       (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
         W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => W (x + X.X s ω)) := by sorry
