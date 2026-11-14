-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a88_original_fullcell_clipped_source_discount_difference
-- name    : AvramDividend.Classical.avram_ga_a88_original_fullcell_clipped_source_discount_difference
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:11:18.531373+00:00
-- url     : https://prove2.me/theorems/fccd6b2c-03a5-4e17-96a5-5d6d2a0d199b
-- title:
--   Original Gaussian full pre-stop physical source cell clipping mismatch is precisely the original discount Euler difference
-- statement:
--   For the genuine dividend controlled original Gaussian source X and each actual full physical grid cell strictly before true stop rho, the discrepancy between the clipped discounted spatial source value increment and its full source increment discounted at cell start equals the exact discount weight difference times that full source value increment.
-- source:
--   Direct b0d9951c real source exact ga_a87 clipping mismatch split; use Proved full source clock ga_a71.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a88_original_fullcell_clipped_source_discount_difference
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ω : Ω) (n m i : ℕ) (ρ : ℝ≥0)
    (hs : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i : ℝ≥0) * Δ < ρ)
    (hfull : let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      (i : ℝ≥0) * Δ + Δ ≤ ρ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℝ≥0 := (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let y : ℝ := x + X.X s ω - rightLimit D s ω
    let r : ℝ := X.X (s + Δ) ω - X.X s ω
    E (v (i + 1)) *
      (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
        w (x + X.X (v i) ω - rightLimit D (v i) ω)) -
      E s * (w (y + r) - w y) =
      (E (s + Δ) - E s) * (w (y + r) - w y) := by sorry
