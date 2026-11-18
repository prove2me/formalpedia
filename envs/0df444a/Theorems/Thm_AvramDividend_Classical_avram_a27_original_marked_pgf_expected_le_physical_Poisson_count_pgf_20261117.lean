-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_original_marked_pgf_expected_le_physical_Poisson_count_pgf_20261117
-- name    : AvramDividend.Classical.avram_a27_original_marked_pgf_expected_le_physical_Poisson_count_pgf_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:24:03.496605+00:00
-- url     : https://prove2.me/theorems/9846a62a-173b-4c8b-9a38-72027dc9f516
-- title:
--   Original negative marked-jump joint PGF expectation is bounded by its actual physical Poisson count PGF
-- statement:
--   For any finite-activity spectrally negative Levy process on its original filtered probability space, when K is a measurable representative of a Poisson(r) physical negative jump count and J is its actual physical cumulative jump sum, the joint generating function at 0<=z<=1 and theta>=0 is at most exp(r(z-1)). This follows because every actual negative jump exponential is at most one, and the source-space Poisson count PGF is exact. No independent marking assumption is introduced.
-- source:
--   Proved original source A85, cc395132, original HasLaw PGF 009ff568; finite probability and integral monotonicity.

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.Probability.HasLaw
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a85_original_physical_negative_jump_exponential_integrable_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_negative_jump_joint_count_pgf_integrable_20261117
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_physical_count_HasLaw_pgf_exact_20261117
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a27_original_marked_pgf_expected_le_physical_Poisson_count_pgf_20261117
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (t : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ)
    (J : Ω → ℝ) (hJMeas : Measurable J)
    (hJEq : J =ᵐ[P] fun ω =>
      ∑' u : ℝ≥0, if 0 < u ∧ u ≤ t then
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u
      else 0)
    (K : Ω → ℕ) (hK : Measurable K)
    (r : ℝ≥0) (hLaw : HasLaw K (poissonMeasure r) P)
    (z : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1) :
    (∫ ω, z ^ (K ω) * Real.exp (θ * J ω) ∂P) ≤
      Real.exp ((r : ℝ) * (z - 1)) := by sorry
