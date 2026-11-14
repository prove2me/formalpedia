-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a195_original_physical_full_raw_square_pointwise_le_prefix_energy
-- name    : AvramDividend.Classical.avram_ga_a195_original_physical_full_raw_square_pointwise_le_prefix_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T16:13:05.868118+00:00
-- url     : https://prove2.me/theorems/99c283b1-5242-44ed-b216-0ab933298013
-- title:
--   Original true full pre-stop Gaussian physical raw-square energy dominated by stopped centred-square energy plus deterministic drift
-- statement:
--   For the original zero-jump or general spectrally negative Lévy process X, the sum of squared raw increments on the physically complete pre-stop uniform mesh is bounded pathwise by twice the centred squared increment energy on the true stopped prefix plus twice the number of cells times the deterministic drift-step square. The source process and full/pre-stop masks are preserved. Uses already Proved Gaussian finite-mask raw-square estimate ga57 and is the uniform-energy input for positive Taylor a149 and discount a151.
-- source:
--   Proved ga57 original Gaussian raw-square versus centred energy inequality and finite monotone mask restriction.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a57_true_stop_raw_quadratic_energy_finset_bound
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a195_original_physical_full_raw_square_pointwise_le_prefix_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (n m : ℕ) (ρ : Ω → ℝ≥0) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℝ≥0 := fun i => (i : ℝ≥0) * Δ
    let Z : ℕ → ℝ := fun i =>
      X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c
    (∑ i ∈ Finset.range m,
        if s i < ρ ω ∧ s i + Δ ≤ ρ ω then
          (Z i + (Δ : ℝ) * X.c)^2 else 0) ≤
      2 * (∑ i ∈ Finset.range m,
        if s i < ρ ω then (Z i)^2 else 0) +
      2 * (m : ℝ) * ((Δ : ℝ) * X.c)^2 := by sorry
