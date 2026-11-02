-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
-- name    : AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T23:47:50.007017+00:00
-- url     : https://prove2.me/theorems/58eec8bb-a471-4313-82af-63f753ab0aba
-- title:
--   Original right-continuous Gaussian quadratic martingale difference has true L1 and conditional mean zero
-- statement:
--   For the actual original zero-jump SpectrallyNegativeLevy X with arbitrary sigma >=0 including zero, deterministic s<=t, the centered quadratic increment Y^2-(t-s)*sigma^2 is genuinely integrable and has zero conditional expectation given the original right-continuous F_s. Derive directly from the already Proved source conditional variance and conditional expectation of constants, using the linearity of condExp_sub. This is the exact source Gaussian second-order finite-cell compensator, not a claim of pathwise quadratic variation for a general jump-bearing process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_rightCont_gaussian_deterministic_increment_condExp_variance

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_rightCont_gaussian_deterministic_quadratic_residual_condExp_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (s t : ℝ≥0) (hst : s ≤ t) :
    let Y : Ω → ℝ := fun ω => X.X t ω - X.X s ω - ((t - s) : ℝ) * X.c
    Integrable (fun ω => Y ω ^ 2 - ((t - s) : ℝ) * X.σ ^ 2) P ∧
      (P[(fun ω => Y ω ^ 2 - ((t - s) : ℝ) * X.σ ^ 2) |
          𝓕.rightCont s] =ᵐ[P] (fun _ => (0 : ℝ))) := by
  sorry
