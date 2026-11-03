-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_predictable_borel_negative_generator_mark_integral_measurable
-- name    : AvramDividend.Classical.avram_wave7_07_original_predictable_borel_negative_generator_mark_integral_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:33:17.928712+00:00
-- url     : https://prove2.me/theorems/62db8f95-9529-4276-86df-252d92e70dbf
-- title:
--   Original stopped predictable nonlinear negative Lévy generator mark integral is measurable on any Borel negative cutoff
-- statement:
--   For any Borel B within the original negative jump marks, the source predictable stopped compact C² generator-integrand integral over B is measurable in time and sample ω under the original right-continuous predictable filtration. Prove by thinning the accepted HS Taylor kernel with B, using its exact integrated identity with generator G, and transporting the mark integral from Iio 0 to B.
-- source:
--   W7-07 exact original source mark-integral predictability bridge to W7-08 and true-clock L1 tails.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_thinned_C2_generator_kernel_L1_identification

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_predictable_borel_negative_generator_mark_integral_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
      ∫ z in B, G (p,z) ∂X.ν) := by sorry
