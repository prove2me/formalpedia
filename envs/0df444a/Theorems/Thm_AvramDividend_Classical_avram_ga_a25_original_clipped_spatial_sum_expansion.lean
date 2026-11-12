-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a25_original_clipped_spatial_sum_expansion
-- name    : AvramDividend.Classical.avram_ga_a25_original_clipped_spatial_sum_expansion
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T00:21:43.141414+00:00
-- url     : https://prove2.me/theorems/bf806cb2-0e25-4797-ab5d-a460cd74a311
-- title:
--   Original clipped zero-jump spatial Taylor residual equals finite sum of exact cell errors
-- statement:
--   For the exact original X.X and rightLimit dividend process on the stopped spatial grid, the finite spatial Taylor-generator residual is the finite sum of physical single-cell remainder, exponential weight-change and Gaussian drift cross terms. The proof sums the established source-specific cell expansion, preserving the clipping at the stopping time.
-- source:
--   A finite-sum consequence of Proved gledger175 47029eeb. This isolates the exact clipped process identity needed before comparing the deterministic full-step Gaussian compensators and the last crossing cell in gledger179.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a25_original_clipped_spatial_sum_expansion
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (m n : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) (ρ ω)
    let L : ℝ≥0 → ℝ≥0 → ℝ := fun s t =>
      let δ : ℝ := ((t - s : ℝ≥0) : ℝ)
      let E : ℝ := Real.exp (-(q * (s : ℝ)))
      let F : ℝ := Real.exp (-(q * (t : ℝ)))
      let y : ℝ := x + X.X s ω - rightLimit D s ω
      let Z : ℝ := x + X.X t ω - rightLimit D s ω
      let z : ℝ := X.X t ω - X.X s ω - δ * X.c
      F * (w Z - w y) -
        E * (deriv w y * z +
          (iteratedDeriv 2 w y / 2) * (z ^ 2 - δ * X.σ ^ 2)) -
        δ * E * X.generator w y
    let R : ℝ≥0 → ℝ≥0 → ℝ := fun s t =>
      let δ : ℝ := ((t - s : ℝ≥0) : ℝ)
      let E : ℝ := Real.exp (-(q * (s : ℝ)))
      let F : ℝ := Real.exp (-(q * (t : ℝ)))
      let y : ℝ := x + X.X s ω - rightLimit D s ω
      let Z : ℝ := x + X.X t ω - rightLimit D s ω
      let z : ℝ := X.X t ω - X.X s ω - δ * X.c
      (F - E) * (w Z - w y) +
        E * (w Z - w y - deriv w y * (z + X.c * δ) -
          (iteratedDeriv 2 w y / 2) * (z + X.c * δ) ^ 2) +
        E * iteratedDeriv 2 w y * (X.c * δ * z + X.c ^ 2 * δ ^ 2 / 2)
    (∑ i ∈ Finset.range (m + 1), L (v i) (v (i + 1))) =
      ∑ i ∈ Finset.range (m + 1), R (v i) (v (i + 1)) := by sorry
