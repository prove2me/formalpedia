-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a65_original_discounted_zerojump_stopmask_generator_variance_grid_identity
-- name    : AvramDividend.Classical.avram_ga_a65_original_discounted_zerojump_stopmask_generator_variance_grid_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:28:21.897626+00:00
-- url     : https://prove2.me/theorems/f71ced2f-c77c-4d5f-a600-e4022af9f251
-- title:
--   Genuine stopped zero-jump Gaussian physical grid discounted variance and generator cancel exactly to the original drift-gradient sum
-- statement:
--   Under the genuine zero-jump original Levy source X and actual D strategy, the discounted stopped physical finite-grid Gaussian quadratic compensator minus HJB generator equals negative actual discounted source drift times value derivative summed on precisely the pre-stop cells.
-- source:
--   Direct true source b0d9951c stopped positive Taylor HJB drift reconciliation using ga_a64.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a65_original_discounted_zerojump_stopmask_generator_variance_grid_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    (∑ i ∈ Finset.range m, if s i < ρ ω then
        E (s i) * (iteratedDeriv 2 w (Y (s i)) / 2 * ((Δ : ℝ) * X.σ ^ 2)) -
          (Δ : ℝ) * E (s i) * X.generator w (Y (s i))
      else 0) =
    (∑ i ∈ Finset.range m, if s i < ρ ω then
      -((Δ : ℝ) * E (s i) * X.c * deriv w (Y (s i)))
    else 0) := by sorry
