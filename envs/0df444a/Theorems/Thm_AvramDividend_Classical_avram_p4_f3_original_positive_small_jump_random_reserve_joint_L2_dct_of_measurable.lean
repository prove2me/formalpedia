-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_small_jump_random_reserve_joint_L2_dct_of_measurable
-- name    : AvramDividend.Classical.avram_p4_f3_original_positive_small_jump_random_reserve_joint_L2_dct_of_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:01:32.592605+00:00
-- url     : https://prove2.me/theorems/9001d86c-d761-4e79-8e51-0f677d9d387f
-- title:
--   Physical original positive-reserve random mesh has vanishing joint small-jump L2 energy
-- statement:
--   For random compact positive-reserve grids converging almost surely, a measurable physical negative small-jump coefficient squared intensity converges to zero in joint probability and the original Levy measure. Uniform original coefficient Q min(1,z²) domination and finite probability mass justify the second dominated-convergence passage.
-- source:
--   Derived from Proved physical original intensity DCT 051d51b7 and two-state domination e4cef933, restricted epsilon<delta. The measurability of the random inner intensity is explicitly a premise to be discharged by the original predictable-grid construction; no law substitution or stochastic process auxiliary is assumed.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_small_jump_mesh_coefficient_L2_dct
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Physical compact reserve mesh convergence in joint probability–Levy small-jump energy. -/

theorem AvramDividend.Classical.avram_p4_f3_original_positive_small_jump_random_reserve_joint_L2_dct_of_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
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
    (hUb : ∀ k ω, U k ω ∈ Icc δ K)
    (hub : ∀ ω, u ω ∈ Icc δ K)
    (hMeasI : ∀ k, Measurable (fun ω =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k ω + z) - w (U k ω)) -
            (w (u ω + z) - w (u ω))) ^ 2) ∂X.ν)))
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => U k ω) atTop (𝓝 (u ω))) :
    Tendsto (fun k =>
      (∫⁻ ω, (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k ω + z) - w (U k ω)) -
            (w (u ω + z) - w (u ω))) ^ 2) ∂X.ν) ∂P))
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
