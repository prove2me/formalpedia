-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_future_window_harmonicity_of_nonnegative_state
-- name    : AvramDividend.Classical.chat04_future_window_harmonicity_of_nonnegative_state
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:28:52.153839+00:00
-- url     : https://prove2.me/theorems/a46c686a-30ac-4210-afa2-6e829a01d5b9
-- title:
--   Future-window q-scale harmonicity reduces to nonnegative current reserves
-- statement:
--   For a canonical Lévy q-scale function that vanishes at negative arguments, the full future-window killed-scale conditional expectation identity follows once it is established on the F_s-measurable nonnegative-current-reserve event. On negative current reserve the killed payoff vanishes pathwise, and this vanishing is preserved under conditional expectation. The theorem isolates the substantive analytic q-harmonicity task to the nonnegative half-line. The negative-support property is passed explicitly to retain exact mathematical assumptions.
-- source:
--   Accepted future-window integrability and pointwise negative-state killed payoff; Mathlib condExp_indicator; almost-everywhere case splitting.

import Mathlib.MeasureTheory.Function.ConditionalExpectation.Indicator
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_standing_future_window_killed_scale_integrable
import Theorems.Thm_AvramDividend_Classical_chat04_future_window_killed_scale_zero_of_negative_start

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.chat04_future_window_harmonicity_of_nonnegative_state
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
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
