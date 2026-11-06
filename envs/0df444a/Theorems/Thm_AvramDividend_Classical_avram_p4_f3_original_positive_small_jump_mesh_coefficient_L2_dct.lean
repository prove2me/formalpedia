-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_positive_small_jump_mesh_coefficient_L2_dct
-- name    : AvramDividend.Classical.avram_p4_f3_original_positive_small_jump_mesh_coefficient_L2_dct
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T17:33:03.692409+00:00
-- url     : https://prove2.me/theorems/051d51b7-86de-4f04-b6db-1730a65d4fc9
-- title:
--   Original strictly positive stopped-reserve small-jump coefficient grid converges in physical L2
-- statement:
--   For compact positive original reserve grids converging to an interior reserve, the physical negative small-jump Levy integral of the squared coefficient difference tends to zero when marks are restricted to (-epsilon,0) with epsilon<delta. This uses original ν, uniform min(1,z^2) domination and pointwise continuity at strictly positive landing reserves, and avoids problematic zero-landing atoms.
-- source:
--   DCT via accepted two-state quadratic domination e4cef933, original ν_integrable, original zero-negative-payoff measurability dabe5048 and positive-reserve sequence continuity. Strict cutoff excludes zero landing; no stochastic isometry or equality in law asserted.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_mark_two_state_squared_difference_dominated
import Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_negative_jump_coefficient_positive_reserve_sequence_continuity
import Theorems.Thm_AvramDividend_Classical_avram_p4_c_generator_zero_negative_payoff_measurable
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

/-- Physical small-jump coefficient square energies converge on strictly positive reserve bands. -/

theorem AvramDividend.Classical.avram_p4_f3_original_positive_small_jump_mesh_coefficient_L2_dct
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
    (U : ℕ → ℝ) (hU : ∀ k, U k ∈ Icc δ K)
    (u : ℝ) (hu : u ∈ Icc δ K)
    (hlim : Tendsto U atTop (𝓝 u)) :
    Tendsto (fun k =>
      (∫⁻ z in Ioo (-ε) (0 : ℝ),
        ENNReal.ofReal
          (((w (U k + z) - w (U k)) -
            (w (u + z) - w u)) ^ 2) ∂X.ν))
      atTop (𝓝 (0 : ℝ≥0∞)) := by sorry
