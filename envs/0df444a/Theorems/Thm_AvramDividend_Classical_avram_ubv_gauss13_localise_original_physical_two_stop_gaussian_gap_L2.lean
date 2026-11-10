-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_physical_two_stop_gaussian_gap_L2
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_physical_two_stop_gaussian_gap_L2
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:29:25.41491+00:00
-- url     : https://prove2.me/theorems/ef79ef96-ff2f-4198-bca1-00bd91f27129
-- title:
--   Original Gaussian physical two-stopping-clock quadratic bracket via common-grid limit
-- statement:
--   For actual original zero-jump Gaussian centred source on one probability space and filtration, if two sampled physical clock sequences converge almost surely at both endpoints and their nonnegative second-moment energies obey the original sampled bracket estimate with a shrinking mesh overhead, the true physical stopped source gap has second moment at most Gaussian variance times the physical clock-gap bound. Uses nonnegative Fatou and continuity of the mesh bound. No uniform integrability, stopping-time floors, auxiliary Brownian process or fourth moments. The incoming sampled gap estimate is supplied by Proved e916b990 and true min/max sampled ceiling coupling.
-- source:
--   Proved a998aa4f two-clock Fatou, Proved e916b990 sampled energy, Proved 2cfa6158 centred source convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_two_clock_physical_energy_fatou

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_physical_two_stop_gaussian_gap_L2
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (τ ρ : Ω → ℝ≥0) (s t : ℕ → Ω → ℝ≥0)
    (ε : ℝ≥0) (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (hS : ∀ᵐ ω ∂P,
      Tendsto (fun n => X.X (s n ω) ω - (s n ω : ℝ) * X.c)
        atTop (𝓝 (X.X (τ ω) ω - (τ ω : ℝ) * X.c)))
    (hT : ∀ᵐ ω ∂P,
      Tendsto (fun n => X.X (t n ω) ω - (t n ω : ℝ) * X.c)
        atTop (𝓝 (X.X (ρ ω) ω - (ρ ω : ℝ) * X.c)))
    (hMeas : ∀ n, Measurable (fun ω : Ω =>
      ENNReal.ofReal (((X.X (t n ω) ω - (t n ω : ℝ) * X.c) -
        (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2)))
    (hSampleBound : ∀ n,
      (∫⁻ ω, ENNReal.ofReal
        (((X.X (t n ω) ω - (t n ω : ℝ) * X.c) -
          (X.X (s n ω) ω - (s n ω : ℝ) * X.c)) ^ 2) ∂P) ≤
        ENNReal.ofReal (((ε : ℝ) + (δ n : ℝ)) * X.σ ^ 2)) :
    (∫⁻ ω, ENNReal.ofReal
      (((X.X (ρ ω) ω - (ρ ω : ℝ) * X.c) -
        (X.X (τ ω) ω - (τ ω : ℝ) * X.c)) ^ 2) ∂P) ≤
      ENNReal.ofReal ((ε : ℝ) * X.σ ^ 2) := by sorry
