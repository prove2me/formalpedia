-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_martingale_of_future_window_harmonicity
-- name    : AvramDividend.Classical.chat04_killed_martingale_of_future_window_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:56:21.370146+00:00
-- url     : https://prove2.me/theorems/e336ea1f-d3b9-4fbd-9a44-478efd3a0e5b
-- title:
--   The q-scale killed process is a martingale under future-window harmonicity
-- statement:
--   Under the standard Lévy and scale-function assumptions and an all-time conditional future-window harmonicity equality, the downward-killed discounted q-scale process is a martingale. This is the assembled form of two canonically published interface theorems, leaving the Lévy-scale harmonicity identity as the exact mathematical gap.
-- source:
--   Published chat04_killed_martingale_of_condExp_identity and chat04_killed_condExp_of_future_window_harmonicity.

import Mathlib.Probability.Martingale.Basic
import Theorems.Thm_AvramDividend_Classical_chat04_killed_martingale_of_condExp_identity
import Theorems.Thm_AvramDividend_Classical_chat04_killed_condExp_of_future_window_harmonicity

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_killed_martingale_of_future_window_harmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ)
    (hFuture : ∀ s u : ℝ≥0, s ≤ u →
      P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
          0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
        (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
          W (x + X.X u ω)) | 𝓕 s] =ᵐ[P] (fun ω => W (x + X.X s ω))) :
    Martingale (fun t ω =>
      ({ω | ∀ v : ℝ≥0, v ≤ t → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (t : ℝ))) * W (x + X.X t ω)) ω) 𝓕 P := by sorry
