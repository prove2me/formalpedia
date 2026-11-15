-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a304_original_true_fullcell_rare_polynomial_expected_L1_vanish_of_integrable
-- name    : AvramDividend.Classical.avram_ga_a304_original_true_fullcell_rare_polynomial_expected_L1_vanish_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:48:21.58719+00:00
-- url     : https://prove2.me/theorems/6ee4352f-0609-40b4-86ea-9b0a83f797d1
-- title:
--   Actual Gaussian full stopped rare polynomial large-cell expectation vanishes by original raw-square tail
-- statement:
--   On the genuine zerojump Gaussian physical grid, the expected nonnegative finite sum of 1+abs(raw increment)+half centered squared increment on wholly stopped cells with abs(raw increment) at least delta tends to zero, provided its finite-mesh integrability. The estimate follows by the exact fullcell source polynomial comparison a303 and the proved original stopped Gaussian rare raw-square L1 result a187. This is the polynomial part of a263 large-cell expected source.
-- source:
--   Original Gaussian a303 exact physical source rare polynomial to square, a186/a187 true stopped raw rare square source integrability and expected L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a303_original_true_fullcell_rare_polynomial_dominated_by_raw_square
import Theorems.Thm_AvramDividend_Classical_avram_ga_a186_original_stopped_Gaussian_raw_large_tail_real_integrable
import Theorems.Thm_AvramDividend_Classical_avram_ga_a187_original_stopped_Gaussian_raw_large_tail_real_L1_vanish
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a304_original_true_fullcell_rare_polynomial_expected_L1_vanish_of_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (hσ : 0 < X.σ) (n : ℕ) (ρ : Ω → ℝ≥0)
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
    (∀ m, Integrable (Poly m) P) →
      Tendsto (fun m => ∫ ω, Poly m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
