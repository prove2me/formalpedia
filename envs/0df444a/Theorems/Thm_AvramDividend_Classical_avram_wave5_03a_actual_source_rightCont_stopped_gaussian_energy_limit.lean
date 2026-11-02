-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_energy_limit
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_source_rightCont_stopped_gaussian_energy_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:31:00.390054+00:00
-- url     : https://prove2.me/theorems/f80d899e-2c5f-4d34-8c75-bb3f7aefa9b5
-- title:
--   Original right-continuous stopped Gaussian source energy has exact small-parameter limit
-- statement:
--   For any original pure-Gaussian Levy source with ν=0 and any bounded right-continuous-filtration stopping time, the actual stopped source exponential quotient at parameter sqrt epsilon has L2 energy tending to h sigma squared. This is a right-continuous stopped transport of the canonically Proved original source variance limit through the same-path Levy lift, including sigma=0. It identifies the original filtration convention but does not claim the continuous martingale quadratic variation process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_energy_small_parameter_limit

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_source_rightCont_stopped_gaussian_energy_limit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    Filter.Tendsto (fun ε : ℝ => (∫ ω,
      ((Real.exp (Real.sqrt ε *
          (X.X (τ ω + h) ω - X.X (τ ω) ω) -
          (h : ℝ) * X.ψ (Real.sqrt ε)) - 1) /
            Real.sqrt ε) ^ 2 ∂P))
      (𝓝[>] (0 : ℝ)) (𝓝 ((h : ℝ) * X.σ ^ 2)) := by
  sorry
