-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a130_original_gaussian_physically_full_mesh_three_error_source_exact_sum
-- name    : AvramDividend.Classical.avram_ga_a130_original_gaussian_physically_full_mesh_three_error_source_exact_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:17:16.686567+00:00
-- url     : https://prove2.me/theorems/3898639f-7a5b-4704-9b84-ac6ca69c9e7a
-- title:
--   Original Gaussian physically full stopped source mesh residual exactly splits into the compact Taylor, centred drift-cross and discount mismatch finite sums
-- statement:
--   For the actual original spectrally negative zero-jump Lévy source X, original dividends D and random stopped physical grid, the sum of pre-stop fully contained cells is exactly the sum of their three source-error components: C2 compact Taylor remainder, raw-centred Gaussian quadratic cross, and discount Euler mismatch. This is a finite algebra identity, valid for each path and mesh, certified by the proved original physical single-cell identity ga128.
-- source:
--   Proved ga128 original Gaussian physical source single-cell three-error identity, and original b0 physically full pre-stop source partition ga94.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a128_original_gaussian_physical_source_full_cell_three_error_exact_algebra
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a130_original_gaussian_physically_full_mesh_three_error_source_exact_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (ω : Ω) (n m : ℕ) (ρ : ℝ≥0) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℕ → ℝ := fun i => x + X.X (s i) ω - rightLimit D (s i) ω
    let R : ℕ → ℝ := fun i => X.X (s i + Δ) ω - X.X (s i) ω
    let Z : ℕ → ℝ := fun i => R i - (Δ : ℝ) * X.c
    let H : ℕ → ℝ := fun i => E (s i) *
      (deriv w (Y i) * Z i + (iteratedDeriv 2 w (Y i) / 2) *
        (Z i^2 - (Δ : ℝ) * X.σ^2)) +
      (Δ : ℝ) * E (s i) * X.generator w (Y i)
    let F : ℕ → ℝ := fun i =>
      E (s i + Δ) * (w (Y i + R i) - w (Y i)) - H i
    let T : ℕ → ℝ := fun i => E (s i) *
      (w (Y i + R i) - w (Y i) - deriv w (Y i) * R i -
        (iteratedDeriv 2 w (Y i) / 2) * R i^2)
    let B : ℕ → ℝ := fun i => E (s i) *
      (iteratedDeriv 2 w (Y i) / 2) * (R i^2 - Z i^2)
    let C : ℕ → ℝ := fun i =>
      (E (s i + Δ) - E (s i)) * (w (Y i + R i) - w (Y i))
    let cut : ℕ → Prop := fun i => s i < ρ ∧ s i + Δ ≤ ρ
    (∑ i ∈ Finset.range m, if cut i then F i else 0) =
      (∑ i ∈ Finset.range m, if cut i then T i else 0) +
      (∑ i ∈ Finset.range m, if cut i then B i else 0) +
      (∑ i ∈ Finset.range m, if cut i then C i else 0) := by sorry
