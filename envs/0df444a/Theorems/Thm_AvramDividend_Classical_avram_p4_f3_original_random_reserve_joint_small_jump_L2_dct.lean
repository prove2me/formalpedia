-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_random_reserve_joint_small_jump_L2_dct
-- name    : AvramDividend.Classical.avram_p4_f3_original_random_reserve_joint_small_jump_L2_dct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T18:25:35.801558+00:00
-- url     : https://prove2.me/theorems/f478d646-b7e5-4f08-a880-771122aa6f19
-- title:
--   Original measurable random positive-reserve mesh has joint Levy small-jump L2 convergence
-- statement:
--   For measurable compact random reserve grids on the original probability space and an almost surely convergent mesh, original Levy small-jump coefficient error converges in joint probability-Levy squared energy. Measurability of the inner intensity is fully discharged from the actual Borel measurable jump coefficient rather than added as a premise.
-- source:
--   Directly combines two original-process source theorems 9001d86c and 8e862de6, each submitted independently; requires both fully Proved before this compositional proof can be accepted, and does not assert a stochastic isometry.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_small_jump_random_reserve_joint_L2_dct_of_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_small_negative_band_random_reserve_coefficient_L2_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_random_reserve_joint_small_jump_L2_dct
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ K ε : ℝ) (hδ : 0 < δ) (hδK : δ ≤ K)
    (hK : ENNReal.ofReal K < C)
    (hε : 0 < ε) (hεδ : ε < δ)
    (U : ℕ → Ω → ℝ) (u : Ω → ℝ)
    (hUb : ∀ k ω, U k ω ∈ Icc δ K)
    (hub : ∀ ω, u ω ∈ Icc δ K)
    (hUMeas : ∀ k, Measurable (U k))
    (huMeas : Measurable u)
    (hlim : ∀ᵐ ω ∂P, Tendsto (fun k => U k ω) atTop (𝓝 (u ω))) :
    Tendsto (fun k =>
      (∫⁻ ω, (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k ω + z) - w (U k ω)) -
            (w (u ω + z) - w (u ω))) ^ 2) ∂X.ν) ∂P))
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
