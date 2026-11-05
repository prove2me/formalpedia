-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_adjacent_joint_laplace
-- name    : AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_adjacent_joint_laplace
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:19:35.651294+00:00
-- url     : https://prove2.me/theorems/219a90bf-46ec-4a4a-bff4-8bca17fd2a85
-- title:
--   Original zero-jump Levy adjacent centred increments have two-parameter Gaussian joint Laplace transform
-- statement:
--   For a zero-jump original Levy source on its genuine probability space, two consecutive drift-centred increments have the full nonnegative-parameter bivariate Gaussian Laplace transform, with separate θ values for the two intervals.
-- source:
--   Proved original adjacent source comap independence and original zero-jump single-interval Gaussian Laplace identity, Mathlib IndepFun.comp and IndepFun.mgf_add'.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_original_adjacent_centred_increments_indep
import Theorems.Thm_AvramDividend_Classical_avram_p4_a_gaussian_zero_jump_original_centred_increment_laplace

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_a_gaussian_zero_jump_original_adjacent_joint_laplace
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Y : SpectrallyNegativeLevy P 𝓕) (hν : Y.ν = 0)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (θf θp : ℝ) (hθf : 0 ≤ θf) (hθp : 0 ≤ θp) :
    (∫ ω, Real.exp
      (θf * ((Y.X u ω - Y.X t ω) - ((u - t : ℝ≥0) : ℝ) * Y.c) +
       θp * ((Y.X t ω - Y.X s ω) - ((t - s : ℝ≥0) : ℝ) * Y.c)) ∂P) =
      Real.exp (((u - t : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θf ^ 2 / 2)) *
      Real.exp (((t - s : ℝ≥0) : ℝ) * (Y.σ ^ 2 * θp ^ 2 / 2)) := by sorry
