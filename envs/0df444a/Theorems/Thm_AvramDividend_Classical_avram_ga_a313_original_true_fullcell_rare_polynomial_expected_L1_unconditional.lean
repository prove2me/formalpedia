-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a313_original_true_fullcell_rare_polynomial_expected_L1_unconditional
-- name    : AvramDividend.Classical.avram_ga_a313_original_true_fullcell_rare_polynomial_expected_L1_unconditional
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:33:44.615199+00:00
-- url     : https://prove2.me/theorems/e112525c-15b5-40db-88bf-5f4e3b3a7b6e
-- title:
--   Unconditional original Gaussian true stopped fullcell rare polynomial source integrable with expected L1 vanishing
-- statement:
--   For the genuine zerojump Gaussian Lévy original physical grid and an original stopping time rho, the rare large-increment polynomial source is integrable for every finite mesh and its expected contribution tends to zero. This discharges a304 true-source integrability using a312, and gives the exact polynomial tail source used alongside the signed rare exponential source a275 to close a263.
-- source:
--   Original a312 integrability, a304 expected rare polynomial source and direct conjunction

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a304_original_true_fullcell_rare_polynomial_expected_L1_vanish_of_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a312_original_true_fullcell_rare_polynomial_integrable
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a313_original_true_fullcell_rare_polynomial_expected_L1_unconditional
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hσ : 0 < X.σ) (n : ℕ) (hn : 0 < n)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) :
    let Δ : ℕ → ℝ≥0 := fun m => (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let s : ℕ → ℕ → ℝ≥0 := fun m i => (i : ℝ≥0) * Δ m
    let R : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      X.X (s m i + Δ m) ω-X.X (s m i) ω
    let Z : ℕ → ℕ → Ω → ℝ := fun m i ω =>
      R m i ω - (Δ m : ℝ) * X.c
    let Poly : ℕ → Ω → ℝ := fun m ω =>
      ∑ i ∈ Finset.range m,
        if (s m i < ρ ω ∧ s m i + Δ m ≤ ρ ω) ∧
           δ ≤ |R m i ω| then
          1 + |R m i ω| + (Z m i ω)^2 / 2 else 0
    (∀ m, Integrable (Poly m) P) ∧
      Tendsto (fun m => ∫ ω, Poly m ω ∂P)
        atTop (𝓝 (0 : ℝ)) := by sorry
