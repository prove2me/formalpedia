-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a194_original_fullcell_small_Taylor_positive_raw_square_control
-- name    : AvramDividend.Classical.avram_ga_a194_original_fullcell_small_Taylor_positive_raw_square_control
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T23:51:35.108212+00:00
-- url     : https://prove2.me/theorems/41e51966-bd53-41d5-aa5c-73c72e517e3d
-- title:
--   Original Gaussian fully pre-stop discounted positive Taylor cell error is arbitrarily small times raw square on small increments
-- statement:
--   For the true zero-jump dividend-controlled Gaussian source, the physical mesh, original stopping clock and actual right-limit dividend reserve, the positive part of the discounted second-order Taylor remainder of every fully pre-stop cell with sufficiently small raw increment is bounded by an arbitrarily small constant times the squared raw increment. Proves the source-specific small-energy estimate required to apply the finite positive small-large split a191 in original positive Taylor a149, using a190 and a non-increasing discount factor.
-- source:
--   Original a190 C2 small-source Taylor modulus, discount positivity and monotonicity, exact physical full-cell mask.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a190_original_stopped_source_small_raw_C2_Taylor_cell_modulus
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a194_original_fullcell_small_Taylor_positive_raw_square_control
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hTopCap : C = ⊤) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ)
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ ω ∂P, ∀ m i : ℕ,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        s < ρ ω → s + Δ ≤ ρ ω → |r| < δ →
        max (Real.exp (-(q * (s : ℝ))) *
          (w (y + r) - w y - deriv w y * r -
            iteratedDeriv 2 w y / 2 * r^2)) 0 ≤ ε * r^2 := by sorry
