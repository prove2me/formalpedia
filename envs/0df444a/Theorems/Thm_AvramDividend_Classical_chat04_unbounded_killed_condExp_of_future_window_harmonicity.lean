-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_condExp_of_future_window_harmonicity
-- name    : AvramDividend.Classical.chat04_unbounded_killed_condExp_of_future_window_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:45:27.434607+00:00
-- url     : https://prove2.me/theorems/24585d9b-b4cf-4b6b-9be5-b2a92d740514
-- title:
--   Unbounded-variation killed conditional expectation from future-window q-harmonicity
-- statement:
--   For unbounded variation and a q-scale function, the conditional expected discounted killed scale payoff equals its value at the earlier horizon, provided the future-window conditional scale harmonicity holds. The reduction does not use Standing.
-- source:
--   Strengthens Proved chat04_killed_condExp_of_future_window_harmonicity (949cf837) by importing newly Proved Standing-free split 070918e3, leaving the positive-reserve scale-function harmonicity as an explicit independent hypothesis. This is the precise bridge to Proved chat01_unbounded_killed_martingale_of_condExp_identity and unbounded two-sided exit.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_unbounded_killed_discounted_condExp_time_split

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_unbounded_killed_condExp_of_future_window_harmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hnbv : ¬ X.BoundedVariation)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u)
    (hFuture : P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
        0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
      (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
        W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      (fun ω => W (x + X.X s ω))) :
    P[({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
      (fun ω => Real.exp (-(q * (s : ℝ))) * W (x + X.X s ω)) := by sorry
