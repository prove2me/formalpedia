-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a215_original_prefix_raw_centered_square_cross_expected_L1
-- name    : AvramDividend.Classical.avram_ga_a215_original_prefix_raw_centered_square_cross_expected_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:31:17.303765+00:00
-- url     : https://prove2.me/theorems/637d25c2-de13-4aab-9543-5efef3a07000
-- title:
--   Original physically stopped Gaussian prefix raw-centred quadratic cross energy integrable and vanishes in expected L1
-- statement:
--   The original Gaussian increments on the physical finite-horizon mesh, masked by the stopping time before each cell, have an integrable absolute raw-centred squared increment cross and its real expectation converges to zero. Derived from the proved original a170 prefix energy package, a81 cross comparison and a86 drift-square mesh estimate, and reused in the a214 exact full-cell transfer.
-- source:
--   Original Gaussian stopped-prefix cross, using a170/a81/a86 proved source theorems.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a81_original_stopped_gaussian_raw_centered_cross_energy_expected_L1_vanish
import Theorems.Thm_AvramDividend_Classical_avram_ga_a86_original_gaussian_uniform_mesh_drift_square_mass_vanish
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a215_original_prefix_raw_centered_square_cross_expected_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hNuZero : X.ν = 0)
    (n : ℕ)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0))) :
    let Cross : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let R : ℝ := X.X (s + Δ) ω - X.X s ω
        let Z : ℝ := R - (Δ : ℝ) * X.c
        if s < ρ ω then |R^2 - Z^2| else 0
    (∀ m : ℕ, Integrable (Cross m) P) ∧
    Tendsto (fun m : ℕ => ∫ ω, Cross m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
