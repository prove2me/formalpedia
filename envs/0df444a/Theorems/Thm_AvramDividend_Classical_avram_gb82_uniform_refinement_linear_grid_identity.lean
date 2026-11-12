-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb82_uniform_refinement_linear_grid_identity
-- name    : AvramDividend.Classical.avram_gb82_uniform_refinement_linear_grid_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T13:48:13.599206+00:00
-- url     : https://prove2.me/theorems/f8452141-5464-423e-a344-91d1f3c3c377
-- title:
--   Two uniform Gaussian linear sums regroup exactly on the product refinement
-- statement:
--   The difference of two linear stochastic sums on arbitrary uniform grids m+1 and p+1 of the same physical path X is exactly the sum of predictable coefficient differences times the centred increments of the common product refinement. This is a pathwise algebraic identity and requires neither stochastic independence nor a replacement Brownian process. The formula is the missing deterministic regrouping step for the original two-grid L2 isometry gbB64 and energy bound gbB60.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gb82_uniform_refinement_linear_grid_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (n : ℕ) (G : ℕ → ℕ → Ω → ℝ) :
    ∀ m p ω,
      let L : ℕ → Ω → ℝ := fun k η =>
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((k + 1 : ℕ) : ℝ≥0)
        let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
        (Finset.range (k + 1)).sum (fun i => G k i η *
          (X.X (s i + Δ) η - X.X (s i) η - (Δ : ℝ) * X.c))
      let N : ℕ := (m + 1) * (p + 1)
      let Δ : ℝ≥0 := (n : ℝ≥0) / (N : ℝ≥0)
      let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
      L m ω - L p ω =
        (Finset.range N).sum (fun r =>
          (G m (r / (p + 1)) ω - G p (r / (m + 1)) ω) *
            (X.X (s r + Δ) ω - X.X (s r) ω - (Δ : ℝ) * X.c)) := by sorry
