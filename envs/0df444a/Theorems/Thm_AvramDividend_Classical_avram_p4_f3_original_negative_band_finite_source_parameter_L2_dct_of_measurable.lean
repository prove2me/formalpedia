-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_band_finite_source_parameter_L2_dct_of_measurable
-- name    : AvramDividend.Classical.avram_p4_f3_original_negative_band_finite_source_parameter_L2_dct_of_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:29:47.100523+00:00
-- url     : https://prove2.me/theorems/ccfb53eb-3740-4f0d-88c1-ced79a312a5f
-- title:
--   Original negative-band random reserve coefficient L2 DCT over arbitrary finite physical source measure
-- statement:
--   For a finite source measure mu on any measurable space, compact positive reserve meshes converging mu-a.e. have converging original negative-band jump coefficients in joint L2 with original X.nu, provided each inner source intensity is measurable. This applies to finite-horizon time-times-original-probability measures, without an independent copy.
-- source:
--   Generalises accepted random probability-and-Levy DCT to arbitrary finite physical source measures: original compact quadratic envelope, original Levy moment integrability, fixed-mark DCT, and outer dominated convergence with finite mu.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_small_jump_mesh_coefficient_L2_dct
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_negative_band_finite_source_parameter_L2_dct_of_measurable
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
    (hUb : ∀ k ω, U k ω ∈ Icc δ K)
    (hub : ∀ ω, u ω ∈ Icc δ K)
    (hMeasI : ∀ k, Measurable (fun ω =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k ω + z) - w (U k ω)) -
            (w (u ω + z) - w (u ω))) ^ 2) ∂X.ν)))
    (hlim : ∀ᵐ ω ∂μ, Tendsto (fun k => U k ω) atTop (𝓝 (u ω))) :
    Tendsto (fun k =>
      (∫⁻ ω, (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k ω + z) - w (U k ω)) -
            (w (u ω + z) - w (u ω))) ^ 2) ∂X.ν) ∂μ))
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
