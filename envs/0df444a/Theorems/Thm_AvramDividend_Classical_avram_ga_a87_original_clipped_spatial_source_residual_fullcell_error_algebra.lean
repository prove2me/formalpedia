-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a87_original_clipped_spatial_source_residual_fullcell_error_algebra
-- name    : AvramDividend.Classical.avram_ga_a87_original_clipped_spatial_source_residual_fullcell_error_algebra
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:10:53.426226+00:00
-- url     : https://prove2.me/theorems/ceed355b-96be-487a-ab36-086bbc10462c
-- title:
--   Original b0d9951c clipped stopped spatial generator residual exactly equals full source compensated Taylor residual plus clipping discount mismatch
-- statement:
--   At every actual original Gaussian physical grid, for original X,D, random stop rho and positive physical time discount, the true clipped stopped spatial HJB residual equals a full physical original-source Gaussian compensated residual plus the precise clipping and discount source mismatch. It is an exact identity, not an approximation.
-- source:
--   Direct b0d9951c original positive interior residual sound parent-level reduction into Proved ga_a78 full-source Gaussian Taylor errors and clipped source time/discount mismatch.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a87_original_clipped_spatial_source_residual_fullcell_error_algebra
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ) (q : ℝ)
    (ρ : Ω → ℝ≥0) (ω : Ω) (n m : ℕ) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let v : ℕ → ℝ≥0 := fun i => min (s i) (ρ ω)
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t =>
      x + X.X t ω - rightLimit D t ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let A : ℕ → ℝ := fun i =>
      E (v (i + 1)) *
        (w (x + X.X (v (i + 1)) ω - rightLimit D (v i) ω) -
          w (Y (v i)))
    let B : ℕ → ℝ := fun i =>
      if s i < ρ ω then E (s i) * (w (Y (s i) + R i) - w (Y (s i)))
      else 0
    let C : ℕ → ℝ := fun i =>
      if s i < ρ ω then E (s i) *
        (deriv w (Y (s i)) * Z i +
          (iteratedDeriv 2 w (Y (s i)) / 2) *
            (Z i^2 - (Δ : ℝ) * X.σ^2)) else 0
    let G : ℕ → ℝ := fun i =>
      if s i < ρ ω then
        (Δ : ℝ) * E (s i) * X.generator w (Y (s i)) else 0
    (∑ i ∈ Finset.range m, A i) -
      (∑ i ∈ Finset.range m, C i) -
      (∑ i ∈ Finset.range m, G i) =
      (∑ i ∈ Finset.range m, (B i - C i - G i)) +
      (∑ i ∈ Finset.range m, (A i - B i)) := by sorry
