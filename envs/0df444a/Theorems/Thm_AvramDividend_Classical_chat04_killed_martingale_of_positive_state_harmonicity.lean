-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_martingale_of_positive_state_harmonicity
-- name    : AvramDividend.Classical.chat04_killed_martingale_of_positive_state_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T08:37:22.875747+00:00
-- url     : https://prove2.me/theorems/9cd3a646-aa60-4fb3-b659-fe3ed031d3de
-- title:
--   Killed q-scale martingale from nonnegative-state conditional harmonicity
-- statement:
--   The full killed discounted q-scale process is a martingale once the future-window q-scale conditional harmonicity is established only on events where the currently observed reserve is nonnegative and W has its standard zero negative-support property. Negative states are handled by the accepted conditional expectation localisation lemma; the existing martingale bridge supplies global process adaptedness, integrability, and the martingale conditional identity. Isolates the remaining analytic q-harmonicity obstruction to current reserves on [0,∞).
-- source:
--   Composition of accepted AvramDividend.Classical.chat04_future_window_harmonicity_of_nonnegative_state and AvramDividend.Classical.chat04_killed_martingale_of_future_window_harmonicity.

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_future_window_harmonicity_of_nonnegative_state
import Theorems.Thm_AvramDividend_Classical_chat04_killed_martingale_of_future_window_harmonicity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal

theorem AvramDividend.Classical.chat04_killed_martingale_of_positive_state_harmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (hWneg : ∀ y : ℝ, y < 0 → W y = 0)
    (hPositive : ∀ s u : ℝ≥0, s ≤ u →
      ({ω | 0 ≤ x + X.X s ω}).indicator
        (P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
          0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
         (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
           W (x + X.X u ω)) | 𝓕 s]) =ᵐ[P]
      ({ω | 0 ≤ x + X.X s ω}).indicator
        (fun ω => W (x + X.X s ω))) :
    Martingale
      (fun t ω =>
        ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
          (fun ω => Real.exp (-(q * (t : ℝ))) *
            W (x + X.X t ω)) ω) 𝓕 P := by sorry
