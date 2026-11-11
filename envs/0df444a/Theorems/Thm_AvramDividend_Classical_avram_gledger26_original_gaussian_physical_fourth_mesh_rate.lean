-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger26_original_gaussian_physical_fourth_mesh_rate
-- name    : AvramDividend.Classical.avram_gledger26_original_gaussian_physical_fourth_mesh_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T16:15:52.940096+00:00
-- url     : https://prove2.me/theorems/deb98b8a-7d01-469f-90c9-7ebbf176b4a7
-- title:
--   Original Gaussian deterministic source mesh fourth energy has explicit inverse-mesh bound
-- statement:
--   For the original zero-jump Levy source X and the deterministic physical uniform mesh of m cells, the normalized fourth-moment energy of the actual centred increments is at most 3 n squared divided by m+1. The result is quantitative and retains original source measurability as an explicit premise, allowing it to be used in compact Taylor large-increment estimates and final overhang control.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gledger22_original_physical_grid_fourth_energy_upper
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gledger26_original_gaussian_physical_fourth_mesh_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0) (hσ : 0 < X.σ)
    (n m : ℕ)
    (hMeas : ∀ i ∈ Finset.range m,
      Measurable (fun ω : Ω =>
        (X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1)) +
          ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
          X.X ((i : ℝ≥0) * ((n : ℝ≥0) / ((m : ℝ≥0) + 1))) ω -
          (((n : ℝ≥0) / ((m : ℝ≥0) + 1)) : ℝ) * X.c) / X.σ)) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let Z : ℕ → Ω → ℝ := fun i ω =>
      (X.X ((i : ℝ≥0) * Δ + Δ) ω -
        X.X ((i : ℝ≥0) * Δ) ω - (Δ : ℝ) * X.c) / X.σ
    (∫⁻ ω, ∑ i ∈ Finset.range m, ENNReal.ofReal ((Z i ω) ^ 4) ∂P) ≤
      ENNReal.ofReal (3 * (n : ℝ) ^ 2 / ((m : ℝ) + 1)) := by sorry
