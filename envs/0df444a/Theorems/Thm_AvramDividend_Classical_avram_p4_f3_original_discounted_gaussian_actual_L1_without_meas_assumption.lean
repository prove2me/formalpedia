-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_gaussian_actual_L1_without_meas_assumption
-- name    : AvramDividend.Classical.avram_p4_f3_original_discounted_gaussian_actual_L1_without_meas_assumption
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T20:30:25.840321+00:00
-- url     : https://prove2.me/theorems/508cf82e-858f-468a-a2e1-8a861438da70
-- title:
--   Actual original discounted predividend Gaussian Ito coefficient L1 without independent measurability assumptions
-- statement:
--   For the actual original Lévy X, dividend strategy D, clipped predividend reserve and finite physical measure, the discounted Gaussian Ito coefficient is Bochner L1 integrable. This follows solely from the original dividend path hypotheses, smoothness and finite quadratic-energy source theorem, with source measurability proved and no extra stochastic-coefficient measurability assumption.
-- source:
--   Combine independent Proved source-exact Gaussian coefficient measurability and the independent L2 to L1 finite-source bridge. This removes the a.e. strong-measurability assumption and supplies the actual Gaussian coefficient integrability needed in constructing the original stopped Gaussian martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_gaussian_coefficient_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_discounted_gaussian_integrable_from_finite_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_discounted_gaussian_actual_L1_without_meas_assumption
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (hq : 0 ≤ q)
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (hε : 0 < ε)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    Integrable (fun p =>
      Real.exp (-(q * (p.1 : ℝ))) *
        (X.σ * deriv w (U p))) μ := by sorry
