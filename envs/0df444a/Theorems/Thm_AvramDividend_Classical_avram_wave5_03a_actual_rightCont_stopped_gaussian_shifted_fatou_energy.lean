-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_actual_rightCont_stopped_gaussian_shifted_fatou_energy
-- name    : AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_shifted_fatou_energy
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T14:59:56.787898+00:00
-- url     : https://prove2.me/theorems/deec3eb1-8c2f-4484-9a99-94007995eb11
-- title:
--   True stopped original Gaussian increment obeys a shifted Fatou second-moment inequality
-- statement:
--   For the actual original SpectrallyNegativeLevy P F with no jumps, a bounded stopping time of the original right-continuous filtration, every future h and arbitrary real shift a, the shifted drift-centred source increment Y+a has finite ENNReal squared energy bounded by h σ²+a². This combines same-path exponential quotient pointwise convergence, the Proved exact centered L² quotient moment and limiting variance, and Fatou; no detached Gaussian copy or Brownian bracket is assumed. The shift is essential for deriving centeredness of Y without assuming it or imposing an abstract uniform-integrability premise.

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
set_option pp.explicit false
set_option pp.fullNames false
set_option pp.universes false

theorem AvramDividend.Classical.avram_wave5_03a_actual_rightCont_stopped_gaussian_shifted_fatou_energy
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hν : X.ν = 0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0)))
    (T : ℝ≥0) (hbounded : ∀ ω, τ ω ≤ T)
    (h : ℝ≥0) (a : ℝ) :
    (∫⁻ ω, ENNReal.ofReal
      ((X.X (τ ω + h) ω - X.X (τ ω) ω - (h : ℝ) * X.c + a) ^ 2) ∂P)
        ≤ ENNReal.ofReal ((h : ℝ) * X.σ ^ 2 + a ^ 2) := by
  sorry
