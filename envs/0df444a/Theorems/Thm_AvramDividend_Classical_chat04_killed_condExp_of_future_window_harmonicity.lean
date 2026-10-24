-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_killed_condExp_of_future_window_harmonicity
-- name    : AvramDividend.Classical.chat04_killed_condExp_of_future_window_harmonicity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:51:30.032003+00:00
-- url     : https://prove2.me/theorems/949cf837-4465-4013-bd40-d4debd251c5d
-- title:
--   Killing-scale conditional expectation from future-window harmonicity
-- statement:
--   Under Standing and the q-scale assumptions, the full killed discounted scale conditional expectation equals the payoff at the earlier time whenever the conditional expectation of the future-window killed q-scale kernel equals the scale function at the current reserve. This bridges the already Proved conditional-expectation time-split identity and the outstanding semigroup harmonicity result.
-- source:
--   Proved chat04_standing_killed_discounted_condExp_time_split; eventual equality and indicator congruence.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_standing_killed_discounted_condExp_time_split

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_killed_condExp_of_future_window_harmonicity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
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
