-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gb51_sigma_zero_original_quadratic_cell_fourth
-- name    : AvramDividend.Classical.avram_gb51_sigma_zero_original_quadratic_cell_fourth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T11:22:35.342447+00:00
-- url     : https://prove2.me/theorems/125ab81e-9638-4d95-95e3-ddce9b740179
-- title:
--   Zero Gaussian original-process quadratic residual cells vanish almost surely
-- statement:
--   In the zero Levy measure and zero Gaussian coefficient case, original drift-centred deterministic mesh increments vanish almost surely. Thus the quadratic residual has integrable square and exactly zero integral at each cell, supplying the sigma zero branch of the uniform intrinsic Gaussian cell fourth moment gb41.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_gb51_sigma_zero_original_quadratic_cell_fourth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hν : X.ν = 0) (hσ : X.σ = 0) (n : ℕ) (hn : 0 < n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (m : ℕ) (i : ℕ), i ∈ Finset.range (m + 1) →
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m + 1 : ℕ) : ℝ≥0)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let R : Ω → ℝ := fun ω =>
        (X.X (s + Δ) ω - X.X s ω - (Δ : ℝ) * X.c) ^ 2 -
          (Δ : ℝ) * X.σ ^ 2
      Integrable (fun ω => (R ω) ^ 2) P ∧
        (∫ ω, (R ω) ^ 2 ∂P) ≤ K / (((m + 1 : ℕ) : ℝ) ^ 2) := by
  sorry
