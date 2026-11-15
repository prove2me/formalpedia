-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a240_original_stopped_fullcell_raw_quadratic_uniform_expected_energy_of_integrable
-- name    : AvramDividend.Classical.avram_ga_a240_original_stopped_fullcell_raw_quadratic_uniform_expected_energy_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:27:49.05735+00:00
-- url     : https://prove2.me/theorems/b6ce7d4c-441a-44e4-b9c6-835f75662fe0
-- title:
--   Actual original Gaussian stopped physical full-cell raw quadratic energy has uniform expected bound assuming finite-grid integrability
-- statement:
--   For the actual original zerojump Gaussian Lévy process on the exact finite-horizon physical grid and a right-continuous stopping time rho, an integrable true fully pre-stop raw second-energy source has expectation bounded uniformly by twice n sigma squared plus twice the square of n times original drift. It follows entirely from original proved stopped Gaussian centered prefix expectation a170, exact source raw square comparison a195 and deterministic finite-mesh drift bound a237 using generic a238, and supplies the uniform small-cell analytic envelope in a216.
-- source:
--   Original a170 source prefix energy, a195 source full versus centered, a237 physical drift and a238 uniform expected transfer

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a195_original_physical_full_raw_square_pointwise_le_prefix_energy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a237_original_physical_mesh_uniform_deterministic_drift_square_energy_bound
import Theorems.Thm_AvramDividend_Classical_avram_ga_a238_integrable_raw_energy_uniform_expected_transfer
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a240_original_stopped_fullcell_raw_quadratic_uniform_expected_energy_of_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω - X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      R m i ω - (Δ m : ℝ) * X.c
    let F : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω
        then (R m i ω)^2 else 0
    (∀ m, Integrable (F m) P) →
      ∀ m, (∫ ω, F m ω ∂P) ≤
        2 * ((n : ℝ) * X.σ^2 + ((n : ℝ) * X.c)^2) := by sorry
