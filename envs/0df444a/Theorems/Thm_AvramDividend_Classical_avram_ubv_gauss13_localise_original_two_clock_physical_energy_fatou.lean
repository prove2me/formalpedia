-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_two_clock_physical_energy_fatou
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_two_clock_physical_energy_fatou
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:11:34.359441+00:00
-- url     : https://prove2.me/theorems/a998aa4f-4e96-4503-8a6d-3a8467c5d16e
-- title:
--   Original Gaussian two physical clocks sampled energy Fatou bound
-- statement:
--   For two original-process centred Gaussian source samples on one indexed sequence of grids, each converging almost surely to a separate true physical stopping clock, the physical quadratic overhang energy is no larger than the liminf of sampled two-clock energies. The interface is necessary to convert Proved 9954ba8b discrete bracket to the physical final stop-straddling cell at a cap or ruin clock. Assumes exact source limits and squared-energy measurability; no local Lean, fourth moment, surrogate Brownian source or stopping-time floor.
-- source:
--   Mathlib Fatou and original spectral-negative Levy X.X. Source limits may be discharged using Proved 2cfa6158; sampled energies with Proved 9954ba8b.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_two_clock_physical_energy_fatou
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ ρ : Ω → ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (hS : ∀ᵐ ω ∂P,
      Tendsto (fun n => X.X (s n ω) ω - (s n ω : ℝ) * X.c)
        atTop (𝓝 (X.X (τ ω) ω - (τ ω : ℝ) * X.c)))
    (hT : ∀ᵐ ω ∂P,
      Tendsto (fun n => X.X (t n ω) ω - (t n ω : ℝ) * X.c)
        atTop (𝓝 (X.X (ρ ω) ω - (ρ ω : ℝ) * X.c)))
    (hMeas : ∀ n, Measurable (fun ω : Ω =>
      ENNReal.ofReal (((X.X (t n ω) ω - (t n ω : ℝ) * X.c) -
        (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2))) :
    (∫⁻ ω, ENNReal.ofReal
      (((X.X (ρ ω) ω - (ρ ω : ℝ) * X.c) -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c)) ^ 2) ∂P) ≤
      Filter.liminf (fun n =>
        ∫⁻ ω, ENNReal.ofReal
          (((X.X (t n ω) ω - (t n ω : ℝ) * X.c) -
            (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2) ∂P)
      atTop := by sorry
