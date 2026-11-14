-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
-- name    : AvramDividend.Classical.avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:51:11.019332+00:00
-- url     : https://prove2.me/theorems/29dedabc-caf4-4157-9016-cc3f1867b7a8
-- title:
--   Original stopped physical Gaussian raw large-square tail is integrable at every mesh
-- statement:
--   For the original zero-jump spectrally negative Lévy source and actual stopping clock, the finite sum over physically spaced pre-stop cells of the squared raw source increments restricted to any large threshold is real-integrable for each mesh. This is derived from the original centred square energy and raw-versus-centred quadratic cross integrability package a170 using a185, preserving actual increments, stopping mask and drift.
-- source:
--   True original source X.X and stopped physical mesh, a170 original stopped second energy and a185 generic masked Gaussian tail integrability.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a170_original_gaussian_prefix_quadratic_cross_integrable_energy_package
import Theorems.Thm_AvramDividend_Classical_avram_ga_a185_gaussian_masked_raw_tail_integrable_of_centered_square_and_cross
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (η : ℝ) :
    let Tail : ℕ → Ω → ℝ := fun m ω =>
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      ∑ i ∈ Finset.range m,
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        if s < ρ ω then (if η ≤ |r| then r^2 else 0) else 0
    ∀ m, Integrable (Tail m) P := by sorry
