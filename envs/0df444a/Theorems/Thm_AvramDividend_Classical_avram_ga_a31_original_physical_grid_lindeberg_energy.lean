-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a31_original_physical_grid_lindeberg_energy
-- name    : AvramDividend.Classical.avram_ga_a31_original_physical_grid_lindeberg_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T22:05:57.500228+00:00
-- url     : https://prove2.me/theorems/bc3e45cc-abea-4c81-98ec-61290a8bcfbb
-- title:
--   Exact original physical Gaussian grid expected large-increment energy is bounded by fourth-moment mesh total
-- statement:
--   Under the original zero-jump process and measurable physical source increments, the expected finite sum of large-normalised-increment quadratic energies is at most the deterministic source Gaussian fourth-moment mesh bound divided by squared threshold.
-- source:
--   Gaussian A original stopped positive-only Taylor large increment control, direct child of Proved ga_a27 and gledger22; root target b0d9951c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a27_lindeberg_scalar_fourth_energy
import Theorems.Thm_AvramDividend_Classical_avram_gledger22_original_physical_grid_fourth_energy_upper
open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a31_original_physical_grid_lindeberg_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0) (hσ : 0 < X.σ)
    (S : Finset ℕ) (s : ℕ → ℝ≥0) (Δ : ℝ≥0)
    (hMeas : ∀ i ∈ S, Measurable (fun ω : Ω =>
      (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ))
    (r : ℝ) (hr : 0 < r) :
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (X.X (s i + Δ) ω - X.X (s i) ω - (Δ : ℝ) * X.c) / X.σ
    (∫⁻ ω, ∑ i ∈ S,
      ENNReal.ofReal (if r ≤ |Z i ω| then (Z i ω) ^ 2 else 0) ∂P) ≤
      ENNReal.ofReal (1 / r ^ 2) *
        (∑ _i ∈ S, ENNReal.ofReal (3 * (Δ : ℝ) ^ 2)) := by sorry
