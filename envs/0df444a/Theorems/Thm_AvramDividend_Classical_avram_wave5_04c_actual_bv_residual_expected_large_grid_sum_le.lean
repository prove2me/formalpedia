-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_expected_large_grid_sum_le
-- name    : AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_expected_large_grid_sum_le
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:42:54.124543+00:00
-- url     : https://prove2.me/theorems/72bebf64-f782-48d4-85df-25043b55bf08
-- title:
--   Expected sum of large BV Lévy residual grid losses is bounded by the actual terminal tail
-- statement:
--   For the actual spectrally negative Lévy source satisfying Standing and BoundedVariation, and any uniform finite grid whose total time nh≤1, the Bochner expectation of the sum of all physical drift residual increments exceeding a real cutoff M is bounded above by the expectation of the similarly truncated terminal physical drift residual R_nh. This uses no extra integrability assumptions: each cell cutoff is Integrable by the genuine source tail-moment theorem, the exactly Proved source stationary-increment law, measurable composition and IdentDistrib.integrable_iff. The finite sum is Integrable, allowing integral_mono_ae applied to the Proved original-process almost-sure large-grid domination. This is a real expectation-interchange ingredient for the C1 generator-semigroup UI bound. The source process X, its physical drift and its actual measure P are unchanged.
-- source:
--   Complete remotely private-probe compiler-verified source candidates/work_on/AvramDividend_04c_actual_residual_expected_grid_tail_probe.lean; no proof submission yet.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_actual_levy_drift_deficit_stationary_increment_law
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_grid_large_increment_sum_le
import Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_actual_bv_residual_tail_integrable_upto_one
set_option autoImplicit false
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave5_04c_actual_bv_residual_expected_large_grid_sum_le
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hX : X.Standing) (hBV : X.BoundedVariation)
    (h : ℝ≥0) (hh : h ≤ 1) (n : ℕ)
    (hn : (n : ℝ≥0) * h ≤ 1) (M : ℝ) :
    (∫ ω, ∑ i ∈ Finset.range n,
      if M < (((((i+1 : ℕ) : ℝ≥0) * h : ℝ) * X.drift -
                X.X (((i+1 : ℕ) : ℝ≥0) * h) ω) -
               (((i : ℝ≥0) * h : ℝ) * X.drift -
                X.X ((i : ℝ≥0) * h) ω))
      then (((((i+1 : ℕ) : ℝ≥0) * h : ℝ) * X.drift -
                X.X (((i+1 : ℕ) : ℝ≥0) * h) ω) -
               (((i : ℝ≥0) * h : ℝ) * X.drift -
                X.X ((i : ℝ≥0) * h) ω))
      else 0 ∂P)
      ≤ ∫ ω, if M < (((n : ℝ≥0) * h : ℝ) * X.drift -
                       X.X ((n : ℝ≥0) * h) ω)
         then (((n : ℝ≥0) * h : ℝ) * X.drift -
                       X.X ((n : ℝ≥0) * h) ω) else 0 ∂P := by sorry
