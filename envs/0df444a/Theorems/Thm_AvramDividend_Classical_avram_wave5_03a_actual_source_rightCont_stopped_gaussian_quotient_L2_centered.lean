-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T09:30:21.645087+00:00
-- url     : https://prove2.me/theorems/e3758fe2-500c-4598-aa2f-1ba5daa133c9
-- title:
--   Actual original source Gaussian quotient is centered L2 after bounded right-continuous stopping
-- statement:
--   For the original SpectrallyNegativeLevy X with zero jump measure, bounded stopping times in the right-continuous filtration F.rightCont (including controlled ruin clocks), and any future horizon h and nonnegative θ, the source-path centred exponential quotient belongs to genuine L2(P) and has mean zero. Use the canonically Proved source Levy right-continuous lift with literally identical X paths and triplet; import the proved bounded-stopping source quotient MemLp and mean-zero theorem on that lift. This provides the correct original-process and original-filtration exact stopping localisation interface without a detached Gaussian copy; it does not assert an Ito integral or continuous bracket.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_stopped_gaussian_exponential_quotient_centered_L2

open MeasureTheory ProbabilityTheory Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (θ : ℝ) (hθ : 0 ≤ θ) :
    MemLp (fun ω => (Real.exp (θ *
      (X.X (τ ω + h) ω - X.X (τ ω) ω) -
      (h : ℝ) * X.ψ θ) - 1) / θ) 2 P ∧
      (∫ ω, (Real.exp (θ *
        (X.X (τ ω + h) ω - X.X (τ ω) ω) -
        (h : ℝ) * X.ψ θ) - 1) / θ ∂P) = 0 := by
  sorry
