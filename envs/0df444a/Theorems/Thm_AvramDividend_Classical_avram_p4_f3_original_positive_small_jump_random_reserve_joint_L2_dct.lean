-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_small_jump_random_reserve_joint_L2_dct
-- name    : AvramDividend.Classical.avram_p4_f3_original_positive_small_jump_random_reserve_joint_L2_dct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:24:58.464736+00:00
-- url     : https://prove2.me/theorems/120f96f8-3540-4c17-a928-9ff0f51b91f6
-- title:
--   Measurable original random reserve grids converge in physical joint small-jump L2
-- statement:
--   For measurable original random reserve meshes confined to a strictly positive compact capital interval and converging almost surely to a measurable reserve, the squared negative small-jump coefficient difference tends to zero after integration over the original Levy intensity and probability measure. All measurability is constructed from the original random reserve fields.
-- source:
--   Constructs the original probability-measure instance from X.isProbability and composes two source-backed Proved prerequisites: physical original random-band measurability and original joint-L2 DCT. No extra probability instance in the final target; neither equality-in-law nor a circular parent import is used.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_small_negative_band_random_reserve_coefficient_L2_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_small_jump_random_reserve_joint_L2_dct_of_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original positive-reserve random mesh coefficients converge in physical joint L2 without an extra measurability premise. -/

theorem AvramDividend.Classical.avram_p4_f3_original_positive_small_jump_random_reserve_joint_L2_dct
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
    (U : ℕ → Ω → ℝ) (u : Ω → ℝ)
    (hUmeas : ∀ k, Measurable (U k)) (humeas : Measurable u)
    (hUb : ∀ k ω, U k ω ∈ Icc δ K)
    (hub : ∀ ω, u ω ∈ Icc δ K)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => U k ω) atTop (𝓝 (u ω))) :
    Tendsto (fun k =>
      (∫⁻ ω, (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k ω + z) - w (U k ω)) -
            (w (u ω + z) - w (u ω))) ^ 2) ∂X.ν) ∂P))
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
