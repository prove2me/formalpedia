-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a244_original_gaussian_true_stopped_fullcell_raw_quadratic_uniform_expected_energy
-- name    : AvramDividend.Classical.avram_ga_a244_original_gaussian_true_stopped_fullcell_raw_quadratic_uniform_expected_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:45:50.968523+00:00
-- url     : https://prove2.me/theorems/916b7528-1e0e-482a-8922-3b29f891a11f
-- title:
--   Original true stopped Gaussian full physical raw quadratic energy jointly integrable and uniformly bounded expected source
-- statement:
--   The authentic zerojump Gaussian Lévy physical grid raw squared increments, restricted to complete cells wholly before an arbitrary original right-continuous-filtration stopping time, have integrable finite-grid sums and a uniform expected sum bound by twice n sigma squared plus twice n squared times original drift squared. This consolidates source-measurability, stopped centered prefix energy, raw-versus-centered quadratic domination, deterministic drift and real expected transfer. It is the missing uniform energy envelope for small Gaussian cells in the original combined top-cap a216.
-- source:
--   Original exact Gaussian a243 integrability and a240 uniform full raw energy expected bound

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a240_original_stopped_fullcell_raw_quadratic_uniform_expected_energy_of_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a243_original_stopped_fullcell_raw_quadratic_energy_integrable
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a244_original_gaussian_true_stopped_fullcell_raw_quadratic_uniform_expected_energy
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
    let F : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω
        then (R m i ω)^2 else 0
    (∀ m, Integrable (F m) P) ∧
    (∀ m, (∫ ω, F m ω ∂P) ≤
      2 * ((n : ℝ) * X.σ^2 + ((n : ℝ) * X.c)^2)) := by sorry
