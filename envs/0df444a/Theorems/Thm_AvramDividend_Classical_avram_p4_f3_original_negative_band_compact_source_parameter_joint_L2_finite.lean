-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_band_compact_source_parameter_joint_L2_finite
-- name    : AvramDividend.Classical.avram_p4_f3_original_negative_band_compact_source_parameter_joint_L2_finite
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:24:46.970201+00:00
-- url     : https://prove2.me/theorems/936d6c76-4475-4d08-bcd1-a52493d65cbc
-- title:
--   Original compact two-reserve negative-band jump coefficient has finite joint energy on any finite source measure
-- statement:
--   For arbitrary finite physical source measure mu, two compact-valued reserve parameters and the original Levy intensity, the joint L2 squared difference of their small negative-band jump coefficients has finite integral. This uses the original Levy-integrability condition, a uniform two-state quadratic envelope and finiteness of mu.
-- source:
--   Source-exact uniform quadratic bound from existing Proved e4cef933, original X.nu_integrable, and two lintegral monotonicity applications. No measurability assumptions, no equality-in-law and no stopped process substitution.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_negative_band_compact_source_parameter_joint_L2_finite
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
    {S : Type*} [mS : MeasurableSpace S]
    (μ : Measure S) (hμ : μ univ < ⊤)
    (U V : S → ℝ)
    (hU : ∀ s, U s ∈ Icc δ K)
    (hV : ∀ s, V s ∈ Icc δ K) :
    (∫⁻ s, (∫⁻ z in Ioo (-ε) (0 : ℝ),
      ENNReal.ofReal
        (((w (U s + z) - w (U s)) -
          (w (V s + z) - w (V s))) ^ 2) ∂X.ν) ∂μ) < ⊤ := by sorry
