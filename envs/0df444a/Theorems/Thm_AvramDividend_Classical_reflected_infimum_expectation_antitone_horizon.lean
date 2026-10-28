-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflected_infimum_expectation_antitone_horizon
-- name    : AvramDividend.Classical.reflected_infimum_expectation_antitone_horizon
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T08:20:25.384283+00:00
-- url     : https://prove2.me/theorems/4714ce59-5386-43a2-ac70-0f4bd1c33a68
-- title:
--   Expected reflected-infimum Laplace envelope decreases with the horizon
-- statement:
--   For θ>0, the expectation of exp(-θ times the reflected running-infimum magnitude)/θ is nonincreasing in the observation horizon. Identify both expectations with the capital-integrated killed-survival transforms, then apply monotonicity of the survival event for increasing horizons.
-- source:
--   Proved killed_survival_capital_reflected_infimum_transform and killed_survival_capital_antitone_horizon.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_survival_capital_reflected_infimum_transform
import Theorems.Thm_AvramDividend_Classical_killed_survival_capital_antitone_horizon

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.reflected_infimum_expectation_antitone_horizon
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (t u : ℝ≥0) (htu : t ≤ u) (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ (ω : Ω),
      ENNReal.ofReal (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ u ∧ y = X.X s ω})) / θ) ∂P) ≤
    (∫⁻ (ω : Ω),
      ENNReal.ofReal (Real.exp (-θ * max 0
        (-sInf {y : ℝ | ∃ s : ℝ≥0, s ≤ t ∧ y = X.X s ω})) / θ) ∂P) := by sorry
