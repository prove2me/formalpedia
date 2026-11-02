-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:54:28.625285+00:00
-- url     : https://prove2.me/theorems/03f483d2-487a-42e1-9261-3a838cf3f358
-- title:
--   Actual rightCont stopped Gaussian drift-centred increment has finite variance energy
-- statement:
--   For the original zero-jump SpectrallyNegativeLevy source and bounded right-continuous stopping time τ, the genuine stopped drift-centred source increment has ENNReal squared moment at most h*σ², without an independent Gaussian copy. Prove by the canonically Proved source pointwise exponential quotient limit, same-source rightCont stopped exponential quotient L2 and energy limit, and Fatou's lemma. This is a rigorous shortest intermediate toward identifying the L2 limit with the original continuous martingale and constructing its quadratic variation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04_source_rightCont_levy_lift
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_stoppedFuturePath_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_source_gaussian_stopped_exponential_quotient_pointwise_drift_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_energy_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_source_rightCont_stopped_gaussian_quotient_L2_centered

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_increment_lintegral_energy_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) :
    (∫⁻ ω, ENNReal.ofReal
      ((X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c) ^ 2) ∂P)
        ≤ ENNReal.ofReal ((h : ℝ) * X.σ ^ 2) := by
  sorry
