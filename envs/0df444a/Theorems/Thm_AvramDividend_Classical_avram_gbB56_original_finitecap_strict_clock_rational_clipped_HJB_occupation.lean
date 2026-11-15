-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB56_original_finitecap_strict_clock_rational_clipped_HJB_occupation
-- name    : AvramDividend.Classical.avram_gbB56_original_finitecap_strict_clock_rational_clipped_HJB_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:25:32.575887+00:00
-- url     : https://prove2.me/theorems/3a3b8b19-580e-4f5e-be20-97540fd85a1f
-- title:
--   Original physical finite-cap rational clipping HJB time source bounded by actual prepayment occupied strip
-- statement:
--   The original jump-free unbounded-variation Gaussian Lévy candidate w with finite admissible cap C has the exact stopped cap-linear generator time drift bounded by the actual prepayment riskProcess upper strip occupation, at every rational interior cap b_j. No additional HJB or positivity premises are required beyond the original candidate assumptions; original stopped clock, D and its right limits are retained.
-- source:
--   Apply B55 to prove the rational clipping nonnegative candidate payoff and HJB below b_j, then use B51 genuine strict-clock postpayment generator to prepayment occupation inequality on the actual original physical stopped measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB51_original_stopped_gaussian_generator_le_true_prepayment_occupation
import Theorems.Thm_AvramDividend_Classical_avram_gbB55_original_rational_caplinear_cutoff_HJB_and_positive_payoff
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB56_original_finitecap_strict_clock_rational_clipped_HJB_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω t, 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q)
    (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw0 : 0 ≤ w 0) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y →
      ENNReal.ofReal y < C → 1 ≤ deriv w y)
    (j : ℕ) :
    let b : ℝ := C.toReal *
      (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
    ∀ᵐ ω ∂P,
      let S : Set ℝ := {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
      let Y : ℝ → ℝ := fun t =>
        x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
      let V : ℝ → ℝ := fun z =>
        if z ≤ b then w z else w b + (z - b)
      Integrable (fun t => X.generator V (Y t) - q * V (Y t))
        (volume.restrict S) →
      Integrable (fun t => if b < Y t then max X.c 0 else 0)
        (volume.restrict S) →
      Integrable (fun t =>
        if b < riskProcess X x D (Real.toNNReal t) ω
        then max X.c 0 else 0)
        (volume.restrict S) →
      (∫ t, X.generator V (Y t) - q * V (Y t) ∂(volume.restrict S)) ≤
        (∫ t, if b < riskProcess X x D (Real.toNNReal t) ω
          then max X.c 0 else 0 ∂(volume.restrict S)) := by sorry
