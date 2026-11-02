-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_increment_tail_stationary_integral
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_increment_tail_stationary_integral
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:30:39.813551+00:00
-- url     : https://prove2.me/theorems/e9958a03-531c-4d4c-b250-4720a559039d
-- title:
--   Actual Lévy drift-deficit large-increment expected tail is stationary at each elapsed time
-- statement:
--   For the original spectrally negative Lévy process X, the Bochner expectation of the threshold-truncated physical drift-residual increment over any interval [s,t] is equal to the expectation of the same truncated residual over elapsed time t-s. This follows by postcomposing the already Proved actual_levy_drift_deficit_stationary_increment_law with the measurable threshold map z ↦ (if M < z then z else 0), then applying equality of integrals for identically distributed maps. The theorem makes no new stochastic assumptions and is the precise expectation-interchange ingredient for source BV first-moment uniform-integrability estimates.
-- source:
--   Complete remote-compiler private-probe-verified source candidates/work_on/AvramDividend_04c_actual_residual_tail_stationary_integral_probe.lean; not yet submitted.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_increment_tail_stationary_integral
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (M : ℝ) :
    (∫ ω,
      if M < (X.drift * (t : ℝ) - X.X t ω) -
             (X.drift * (s : ℝ) - X.X s ω)
      then (X.drift * (t : ℝ) - X.X t ω) -
             (X.drift * (s : ℝ) - X.X s ω) else 0 ∂P)
    = (∫ ω,
      if M < X.drift * ((t - s : ℝ≥0) : ℝ) - X.X (t-s) ω
      then X.drift * ((t - s : ℝ≥0) : ℝ) - X.X (t-s) ω
      else 0 ∂P) := by sorry
