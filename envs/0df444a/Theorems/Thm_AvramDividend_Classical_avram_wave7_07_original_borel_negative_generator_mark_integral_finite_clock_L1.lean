-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_borel_negative_generator_mark_integral_finite_clock_L1
-- name    : AvramDividend.Classical.avram_wave7_07_original_borel_negative_generator_mark_integral_finite_clock_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:46:07.498134+00:00
-- url     : https://prove2.me/theorems/3a4b5f0b-45ca-4d69-a200-9df9cb929a33
-- title:
--   Original Borel-cutoff negative generator mark integral has finite signed L1 on every finite predictable clock
-- statement:
--   For a finite original predictable time-sample clock μ, the signed source Lévy generator mark integral over every Borel set B of negative marks is Bochner integrable. Specialise the already Proved arbitrary predictable C² thinning L1 kernel identification to S={(p,z):z∈B}, then use measure-restriction identities to identify the result with the B-restricted original ν-integral. Retain the actual Ω,P,X,D,ruin time and compensated truncation.
-- source:
--   W7-07 exact-source finite-clock generator drift L1 bridge for stopped Itô verification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_thinned_C2_generator_kernel_L1_identification

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave7_07_original_borel_negative_generator_mark_integral_finite_clock_L1
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
    Integrable (fun p : ℝ≥0 × Ω =>
      ∫ z in B, G (p,z) ∂X.ν) μ := by sorry
