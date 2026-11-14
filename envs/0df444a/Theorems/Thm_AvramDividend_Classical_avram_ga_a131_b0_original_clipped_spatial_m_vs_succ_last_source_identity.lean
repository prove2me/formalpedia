-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a131_b0_original_clipped_spatial_m_vs_succ_last_source_identity
-- name    : AvramDividend.Classical.avram_ga_a131_b0_original_clipped_spatial_m_vs_succ_last_source_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:26:07.305515+00:00
-- url     : https://prove2.me/theorems/9113a95e-0232-46b9-aef4-1757b5826c69
-- title:
--   Original Gaussian spatial source m+1 clipped value sum differs from actual b0 m-cell root by exactly one last physical cell
-- statement:
--   For the same original Gaussian source X and admissible dividend right limits, on the same m-dependent uniform mesh and actual clipped stop clock rho, the earlier integrability theorem uses a sum over m+1 clipped source value increments while b0 uses m. Their difference is exactly the final i=m source increment. The identity makes the finite-mesh integrability correction explicit without changing the original clock or Gaussian process.
-- source:
--   Original b0 positive interior root and proved earlier ga26 original spatial positive integrability m+1-cell statement; Finset.sum_range_succ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a131_b0_original_clipped_spatial_m_vs_succ_last_source_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ} (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (w : ℝ → ℝ)
    (q : ℝ) (n m : ℕ) (ρ : ℝ≥0) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : ℕ → ℝ≥0 := fun i => min ((i : ℝ≥0) * Δ) ρ
    let E : ℝ≥0 → ℝ := fun t => Real.exp (-(q * (t : ℝ)))
    let Y : ℝ≥0 → ℝ := fun t => x + X.X t ω - rightLimit D t ω
    let Z : ℕ → ℝ := fun i =>
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    (∑ i ∈ Finset.range (m + 1),
      E (v (i + 1)) * (w (Z i) - w (Y (v i)))) =
    (∑ i ∈ Finset.range m,
      E (v (i + 1)) * (w (Z i) - w (Y (v i)))) +
    E (v (m + 1)) * (w (Z m) - w (Y (v m))) := by sorry
