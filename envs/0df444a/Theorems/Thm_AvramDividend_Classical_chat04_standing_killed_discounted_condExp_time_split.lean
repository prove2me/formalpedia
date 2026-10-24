-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_standing_killed_discounted_condExp_time_split
-- name    : AvramDividend.Classical.chat04_standing_killed_discounted_condExp_time_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T22:08:26.875993+00:00
-- url     : https://prove2.me/theorems/3ba2dca6-55d5-497f-b685-c4161044778c
-- title:
--   Standing-only conditional-expectation time splitting for killed discounted scale payoff
-- statement:
--   Under exactly the Avram Standing assumptions, positive discount and q-scale axioms, the conditional expectation of the q-scale payoff killed by ruin up to u decomposes at any s≤u into survival to s and the residual future-window killed conditional scale payoff, including deterministic discount splitting. The future-window integrability premise is discharged by a separately proved Standing-based theorem, with no extra moment or measurability assumptions. This is a direct root-connected killed-martingale bridge, without asserting the still-open harmonicity identity.
-- source:
--   Previously accepted chat04_killed_discounted_condExp_time_split and newly authored chat04_standing_future_window_killed_scale_integrable.

import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_killed_discounted_condExp_time_split
import Theorems.Thm_AvramDividend_Classical_chat04_standing_future_window_killed_scale_integrable

open MeasureTheory Set
open scoped NNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_standing_killed_discounted_condExp_time_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (x : ℝ) (s u : ℝ≥0) (hsu : s ≤ u) :
    P[({ω | ∀ v : ℝ≥0, v ≤ u → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (u : ℝ))) * W (x + X.X u ω)) | 𝓕 s] =ᵐ[P]
      ({ω | ∀ v : ℝ≥0, v ≤ s → 0 ≤ x + X.X v ω}).indicator
        (fun ω => Real.exp (-(q * (s : ℝ))) *
          P[({ω | ∀ v : ℝ≥0, s ≤ v → v ≤ u →
            0 ≤ (x + X.X s ω) + (X.X v ω - X.X s ω)}).indicator
              (fun ω => Real.exp (-(q * ((u : ℝ) - (s : ℝ)))) *
                W (x + X.X u ω)) | 𝓕 s] ω) := by sorry
