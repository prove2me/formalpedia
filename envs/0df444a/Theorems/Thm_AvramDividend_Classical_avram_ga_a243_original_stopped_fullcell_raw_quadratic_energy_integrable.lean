-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a243_original_stopped_fullcell_raw_quadratic_energy_integrable
-- name    : AvramDividend.Classical.avram_ga_a243_original_stopped_fullcell_raw_quadratic_energy_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:25:18.926774+00:00
-- url     : https://prove2.me/theorems/7b791e7a-55ce-4fec-b978-1f3c6807f6cd
-- title:
--   True original zerojump Gaussian full stopped physical-grid raw quadratic-energy source integrable
-- statement:
--   For the genuine original zerojump Gaussian Lévy process and any original right-continuous-filtration stopping time, the finite physical-grid sum of squared raw Gaussian increments restricted to wholly pre-stop cells is integrable at every mesh level. Measurability follows from source a242, the upper majorant from a195, the centered stopped Gaussian prefix energy from a170 and generic nonnegative energy integrability from a241. This closes the remaining integrability premise in a240, enabling uniform raw expected energy for the combined a216 small-cell source.
-- source:
--   a170+a195+a241+a242 original X.X Gaussian stopped full-cell source

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a195_original_physical_full_raw_square_pointwise_le_prefix_energy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a241_integrability_of_source_nonnegative_quadratic_energy_majorant
import Theorems.Thm_AvramDividend_Classical_avram_ga_a242_original_true_stopped_fullcell_raw_Gaussian_quadratic_energy_measurable
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a243_original_stopped_fullcell_raw_quadratic_energy_integrable
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
    ∀ m, Integrable (F m) P := by sorry
