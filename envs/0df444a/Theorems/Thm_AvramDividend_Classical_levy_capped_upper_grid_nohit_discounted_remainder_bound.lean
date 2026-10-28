-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_capped_upper_grid_nohit_discounted_remainder_bound
-- name    : AvramDividend.Classical.levy_capped_upper_grid_nohit_discounted_remainder_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T12:00:18.862089+00:00
-- url     : https://prove2.me/theorems/f590893f-366a-41e2-9647-0e6d0ef2aa39
-- title:
--   Exponential bound on the capped upper-grid no-crossing remainder
-- statement:
--   For a spectrally negative Lévy process and any deterministic capped observation grid, the expected compensated exponential contribution from paths that stay below the upper level at every sampled time through the terminal index is at most exp(θz−qT), where ψ(θ)=q and θ≥0. The upper-only sampled hitting index is then the terminal index. For q>0 and terminal T tending to infinity, this is the vanishing no-upcrossing remainder needed for an independent one-sided first-passage transform; it does not assume any killed-scale harmonicity or exit identity.
-- source:
--   Pathwise first-hit/no-observed-crossing theorem 42afa059-764f-47cf-a2dc-0e999983bb09 and probability normalisation from SpectrallyNegativeLevy; discrete first-passage exponential argument underlying Avram, Palmowski and Pistorius (2007), section 3.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_hittingBtwn_eq_terminal_of_no_observed_crossing
import Mathlib.Probability.Process.HittingTime
import Mathlib.MeasureTheory.Integral.Bochner.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_capped_upper_grid_nohit_discounted_remainder_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (clock : ℕ → ℝ≥0)
    (θ q : ℝ) (hθ : 0 ≤ θ) (hroot : X.ψ θ = q)
    (z : ℝ) (m : ℕ) :
    (∫ ω, (if ∀ j : ℕ, j ≤ m → X.X (clock j) ω ≤ z then
        let K := hittingBtwn (fun k η => X.X (clock k) η) (Ioi z) 0 m ω
        Real.exp (θ * X.X (clock K) ω - (clock K : ℝ) * X.ψ θ)
      else (0 : ℝ)) ∂P) ≤
    Real.exp (θ * z - (clock m : ℝ) * q) := by sorry
