-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a137_original_physical_fullcell_positive_Taylor_cross_discount_pointwise_bound
-- name    : AvramDividend.Classical.avram_ga_a137_original_physical_fullcell_positive_Taylor_cross_discount_pointwise_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:32:30.72414+00:00
-- url     : https://prove2.me/theorems/77dba442-69c0-4209-aec6-4da674e2b400
-- title:
--   Genuine original Gaussian physical full-cell positive residual bounded by one-sided classical Taylor, absolute Hessian cross and one-sided discount finite sums
-- statement:
--   At every original stopped Gaussian physical mesh and on each original sample path, the positive part of the total full pre-stop compensated spatial residual is bounded by the positive part of the classical C2 Taylor remainder finite sum, the absolute raw-centred Hessian quadratic cross sum and the positive part of the discount mismatch finite sum. The identity ga130 is already certified for actual source X and D, so only the sharp one-sided scalar triangle inequality remains.
-- source:
--   Certified original source Gaussian physical full finite grid 3-error ga130. Supports the exact root positive fullcell expected L1 source goal ga134.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a130_original_gaussian_physically_full_mesh_three_error_source_exact_sum
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a137_original_physical_fullcell_positive_Taylor_cross_discount_pointwise_bound
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
    max (∑ i ∈ Finset.range m, if cut i then F i else 0) 0 ≤
      max (∑ i ∈ Finset.range m, if cut i then T i else 0) 0 +
      |∑ i ∈ Finset.range m, if cut i then B i else 0| +
      max (∑ i ∈ Finset.range m, if cut i then C i else 0) 0 := by sorry
