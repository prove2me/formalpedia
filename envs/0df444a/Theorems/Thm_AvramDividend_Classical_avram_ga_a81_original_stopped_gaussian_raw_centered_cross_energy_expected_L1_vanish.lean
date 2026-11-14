-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a81_original_stopped_gaussian_raw_centered_cross_energy_expected_L1_vanish
-- name    : AvramDividend.Classical.avram_ga_a81_original_stopped_gaussian_raw_centered_cross_energy_expected_L1_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T07:52:35.063257+00:00
-- url     : https://prove2.me/theorems/6f76bf53-0038-4408-a576-64fabe274a5d
-- title:
--   Original stopped Gaussian raw-centred source quadratic drift cross correction vanishes in expected absolute L1
-- statement:
--   For actual physical Gaussian source increments on the true stopping-clock mask, if expected centred squared source increments have a uniform bound and the total deterministic squared physical mesh drift vanishes, the expected total absolute raw-versus-centred squared increment difference converges to zero.
-- source:
--   Direct original b0d9951c compensated Gaussian spatial source error cross term from ga_a77/78, using Proved ga_a80 and ga_a59.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_a81_original_stopped_gaussian_raw_centered_cross_energy_expected_L1_vanish
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (s : ℕ → ℕ → ℝ≥0) (ρ : Ω → ℝ≥0)
    (Z : ℕ → ℕ → Ω → ℝ) (d : ℕ → ℝ)
    (K : ℝ) (hK : 0 ≤ K)
    (hAI : ∀ m : ℕ, Integrable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if s m i < ρ ω then
        |(Z m i ω + d m)^2 - (Z m i ω)^2| else 0) P)
    (hEI : ∀ m : ℕ, Integrable (fun ω : Ω =>
      ∑ i ∈ Finset.range m, if s m i < ρ ω then
        (Z m i ω)^2 else 0) P)
    (hEBound : ∀ m : ℕ,
      (∫ ω, (∑ i ∈ Finset.range m, if s m i < ρ ω then
        (Z m i ω)^2 else 0) ∂P) ≤ K)
    (hDriftMass : Tendsto (fun m : ℕ => (m : ℝ) * (d m)^2)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m : ℕ => ∫ ω, (∑ i ∈ Finset.range m,
      if s m i < ρ ω then
        |(Z m i ω + d m)^2 - (Z m i ω)^2|
      else 0) ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
