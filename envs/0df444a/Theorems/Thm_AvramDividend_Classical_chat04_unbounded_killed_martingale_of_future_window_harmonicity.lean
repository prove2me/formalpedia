-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_martingale_of_future_window_harmonicity
-- name    : AvramDividend.Classical.chat04_unbounded_killed_martingale_of_future_window_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:50:57.95907+00:00
-- url     : https://prove2.me/theorems/4debac27-6d55-4aaa-9eaa-a3dcd68439d9
-- title:
--   Standing-free killed q-scale martingale from future-window harmonicity
-- statement:
--   For a spectrally negative Lévy process of unbounded variation, conditional future-window q-scale harmonicity implies that the discounted downward-killed scale-function payoff is a martingale without Standing hypotheses. This is the exact optional-stopping input for the two-sided-exit identity.
-- source:
--   Source-faithful strengthening of Proved chat04_killed_martingale_of_future_window_harmonicity (e336ea1f), combining Proved chat01_unbounded_killed_martingale_of_condExp_identity (5d347463) with Standing-free killed conditional expectation bridge chat04_unbounded_killed_condExp_of_future_window_harmonicity. The latter is a pending publication and must be Proved before proof submission.

import Mathlib.Probability.Martingale.Basic
import Theorems.Thm_AvramDividend_Classical_chat01_unbounded_killed_martingale_of_condExp_identity
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_condExp_of_future_window_harmonicity

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_unbounded_killed_martingale_of_future_window_harmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
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
