-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_band_finite_source_parameter_L2_dct
-- name    : AvramDividend.Classical.avram_p4_f3_original_negative_band_finite_source_parameter_L2_dct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:36:27.382084+00:00
-- url     : https://prove2.me/theorems/6aa60af4-8f95-4006-a5d9-42ffde9185c0
-- title:
--   Original physical finite-source random reserve small-jump L2 convergence with measurability discharged
-- statement:
--   For original process X and any finite measure on a measurable source parameter S, including finite-horizon physical time-by-original-probability, measurable compact positive reserve mesh values approaching u a.e. have vanishing integrated squared negative-jump coefficient difference. The genuine original Levy-intensity measurability lemma discharges inner-integral measurability.
-- source:
--   Combines accepted arbitrary-source-parameter squared intensity measurability with the finite-source measure original negative band DCT of measurable. All dependencies are original-process finite source lemmas; no source Ito witness or parent imported.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_band_finite_source_parameter_L2_dct_of_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_small_negative_band_arbitrary_source_parameter_L2_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_negative_band_finite_source_parameter_L2_dct
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (hε : 0 < ε) (hεδ : ε < δ)
    {S : Type*} [mS : MeasurableSpace S]
    (μ : Measure S) (hμ : μ univ < ⊤)
    (U : ℕ → S → ℝ) (u : S → ℝ)
    (hUmeas : ∀ k, Measurable (U k)) (humeas : Measurable u)
    (hUb : ∀ k s, U k s ∈ Icc δ K)
    (hub : ∀ s, u s ∈ Icc δ K)
    (hlim : ∀ᵐ s ∂μ, Tendsto (fun k => U k s) atTop (𝓝 (u s))) :
    Tendsto (fun k =>
      (∫⁻ s, (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k s + z) - w (U k s)) -
            (w (u s + z) - w (u s))) ^ 2) ∂X.ν) ∂μ))
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
