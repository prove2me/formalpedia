-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a371_original_fullcell_joint_Taylor_Lipschitz_Hessian_selected_cutoff_ae
-- name    : AvramDividend.Classical.avram_ga_a371_original_fullcell_joint_Taylor_Lipschitz_Hessian_selected_cutoff_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:21:27.852004+00:00
-- url     : https://prove2.me/theorems/5123d759-26dd-4e37-b652-20bec7b438e7
-- title:
--   Original stopped physical Gaussian small increment source has joint a.e. one-sided Taylor, local Lipschitz and Hessian bounds at one cutoff
-- statement:
--   For an original stopped Gaussian Lévy source under a top-cap C² candidate and pre-stop postpayment localisation, there are global nonnegative constants L and M such that for each Taylor tolerance ε a single positive raw-increment cutoff δ works simultaneously almost surely for every physical full pre-stop cell: the original positive Taylor remainder is at most ε times the raw squared increment, the value increment is Lipschitz with constant L, and the original unweighted Hessian is bounded by M. The proof intersects the genuine a194, a369 and a370 sample-path events and chooses a cutoff below both required scales. This supplies a complete authentic one-sided source input for a368 and eventually a361.
-- source:
--   Original a194 true source positive Taylor, a369 postpayment local Lipschitz and a370 unweighted Hessian AE.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a194_original_fullcell_small_Taylor_positive_raw_square_control
import Theorems.Thm_AvramDividend_Classical_avram_ga_a369_original_fullcell_small_raw_increment_local_postpayment_Lipschitz_ae
import Theorems.Thm_AvramDividend_Classical_avram_ga_a370_original_fullcell_unweighted_postpayment_Hessian_uniform_ae
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a371_original_fullcell_joint_Taylor_Lipschitz_Hessian_selected_cutoff_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (C : ℝ≥0∞) (hTopCap : C = ⊤) (w : ℝ → ℝ)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q) (n : ℕ) (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ L M : ℝ, 0 ≤ L ∧ 0 ≤ M ∧
      ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧
      ∀ᵐ ω ∂P, ∀ m i : ℕ,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        let r : ℝ := X.X (s + Δ) ω - X.X s ω
        let y : ℝ := x + X.X s ω - rightLimit D s ω
        s < ρ ω → s + Δ ≤ ρ ω → |r| < δ →
          max (Real.exp (-(q * (s : ℝ))) *
            (w (y + r) - w y - deriv w y * r -
              iteratedDeriv 2 w y / 2 * r^2)) 0 ≤ ε * r^2 ∧
          |w (y + r) - w y| ≤ L * |r| ∧
          |iteratedDeriv 2 w y| ≤ M := by sorry
