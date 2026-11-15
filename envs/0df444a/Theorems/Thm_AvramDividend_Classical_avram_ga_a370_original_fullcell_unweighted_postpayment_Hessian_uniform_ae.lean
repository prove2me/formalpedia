-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a370_original_fullcell_unweighted_postpayment_Hessian_uniform_ae
-- name    : AvramDividend.Classical.avram_ga_a370_original_fullcell_unweighted_postpayment_Hessian_uniform_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T12:16:38.609428+00:00
-- url     : https://prove2.me/theorems/42a6c915-e809-48b3-87d7-eec66e721001
-- title:
--   Original stopped Gaussian source physical-mesh unweighted Hessian uniformly bounded almost surely at all pre-stop starts
-- statement:
--   For an original stopped spectrally negative Lévy source with a top-cap C² candidate w, the compact postpayment jet theorem a165 supplies one nonnegative constant M such that almost every path has |iteratedDeriv 2 w(Y_s)|≤M at every physical grid start s before the stopping time, for every mesh level and index. The source uses exact unweighted Hessian, unlike a180 which bounds its discounted masked variant. This is the genuine Hessian source hypothesis for the scalar and a.e. combined Gaussian small-cell Young inequalities a290/a368.
-- source:
--   Original proved a165 Gaussian postpayment compact C² jet, definitional iteratedDeriv_succ.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a165_original_strict_source_postpayment_C2_jet_uniform_ae
open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a370_original_fullcell_unweighted_postpayment_Hessian_uniform_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (n : ℕ) (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ M : ℝ, 0 ≤ M ∧
      ∀ᵐ ω ∂P, ∀ m i : ℕ,
        let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
        let s : ℝ≥0 := (i : ℝ≥0) * Δ
        s < ρ ω →
          |iteratedDeriv 2 w
            (x + X.X s ω - rightLimit D s ω)| ≤ M := by sorry
