-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_original_weighted_physical_quadratic_cell_L2_uniform_rate
-- name    : AvramDividend.Classical.avram_ga_original_weighted_physical_quadratic_cell_L2_uniform_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-21T00:22:05.704357+00:00
-- url     : https://prove2.me/theorems/17cc346f-ea34-4622-a695-2a04eb099113
-- title:
--   Authentic original Gaussian physical-grid centred-square cell weighted L2 bound at order inverse mesh count squared
-- statement:
--   Let X be the original zero-jump standing spectrally negative Lévy process with Gaussian part and retain its physical uniform grid Δ=n/(m+1). For any random coefficients H_mi uniformly bounded by K, whose products with the centred quadratic increment are square-integrable, there exists J≥0 independent of mesh and cell such that E[(H_mi(Z_mi²−σ²Δ))²]≤J/(m+1)². This is derived from the already Proved original unweighted fourth-moment cell estimate and the nonindependent bounded-weight L2 comparison. With the separately Proved original right-continuous filtration MDS result, this supplies the sharp vanishing second-chaos variance rate for the real finite-cap stopped Hessian coefficients.
-- source:
--   Original physical-grid Gaussian quadratic noise source needed by the true finite-cap stopped Ito–Stieltjes dividend cash estimate. Avoids future-dependent full-cell indicator as martingale mask.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_original_weighted_physical_quadratic_cell_L2_uniform_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (n : ℕ) (hn : 0 < n)
    (H : ℕ → ℕ → Ω → ℝ) (K : ℝ) (hK : 0 ≤ K)
    (hH : ∀ m i ω, |H m i ω| ≤ K)
    (hHI : ∀ m i, i ∈ Finset.range (m + 1) →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      Integrable (fun ω => (H m i ω * ((X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 -
          (Δ : ℝ) * X.σ ^ 2)) ^ 2) P) :
    ∃ J : ℝ, 0 ≤ J ∧ ∀ m i, i ∈ Finset.range (m + 1) →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      (∫ ω, (H m i ω * ((X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 -
          (Δ : ℝ) * X.σ ^ 2)) ^ 2 ∂P) ≤
        J / (((m + 1 : ℕ) : ℝ) ^ 2) := by sorry
