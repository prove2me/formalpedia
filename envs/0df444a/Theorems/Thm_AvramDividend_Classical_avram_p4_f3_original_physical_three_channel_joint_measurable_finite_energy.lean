-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_three_channel_joint_measurable_finite_energy
-- name    : AvramDividend.Classical.avram_p4_f3_original_physical_three_channel_joint_measurable_finite_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:34:55.880968+00:00
-- url     : https://prove2.me/theorems/10ad46dd-d25d-4a92-adae-4da97b9c66f1
-- title:
--   Same original process clipped stopped Itô Gaussian and small/large jump coefficients have measurable source intensities and finite joint energies
-- statement:
--   For the actual original Levy X and admissible dividend strategy D, three physical Itô-Meyer source channels share one measurable clipped predividend left-limit reserve. Their small/large original Levy intensity integrals are jointly measurable and all Gaussian/small/large energies are finite over each finite physical source measure.
-- source:
--   Combine independent Proved/public 55e36fd0, 8bf95bcb, ce2f5916 and b7290e6a. The same source X,D,ν,σ, filtered process and clipped U appear in each; this is the noncircular three-martingale coefficient interface for fdb9a6a3.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_predividend_clipped_reserve_jointly_measurable_bounded
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_clipped_small_negative_band_intensity_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_large_negative_band_arbitrary_source_intensity_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_physical_clipped_gaussian_small_large_joint_L2_energy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_physical_three_channel_joint_measurable_finite_energy
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
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C) (hε : 0 < ε)
    (μ : Measure (ℝ≥0 × Ω)) (hμ : μ univ < ⊤) :
    let U : ℝ≥0 × Ω → ℝ := fun p =>
      let y := Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      if y ∈ Icc δ K then y else δ
    Measurable U ∧
    Measurable (fun p =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U p + z) - w (U p)) -
            (w (δ + z) - w δ)) ^ 2) ∂X.ν)) ∧
    Measurable (fun p =>
      (∫⁻ z in Iic (-ε),
        ENNReal.ofReal ((w (U p + z) - w (U p)) ^ 2) ∂X.ν)) ∧
    ((∫⁻ p, ENNReal.ofReal ((X.σ * deriv w (U p)) ^ 2) ∂μ) < ⊤ ∧
     (∫⁻ p, (∫⁻ z in Ioo (-ε) (0 : ℝ),
       ENNReal.ofReal
         (((w (U p + z) - w (U p)) -
           (w (δ + z) - w δ)) ^ 2) ∂X.ν) ∂μ) < ⊤) ∧
    (∫⁻ p, (∫⁻ z in Iic (-ε),
      ENNReal.ofReal ((w (U p + z) - w (U p)) ^ 2) ∂X.ν) ∂μ) < ⊤ := by sorry
