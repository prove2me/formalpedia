-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_increment_ae_fixed_times
-- name    : AvramDividend.Classical.bv_actual_levy_drift_increment_ae_fixed_times
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:10:10.423857+00:00
-- url     : https://prove2.me/theorems/d7ff2448-4534-4320-b911-51a4c347033a
-- title:
--   Almost-sure drift bound on every prescribed actual Lévy increment
-- statement:
--   For two fixed ordered times s≤t, the actual Lévy increment is almost surely bounded by the drift times their separation. This transfers the Proved fixed-time drift-support inequality through the stationary-increments distribution axiom using IdentDistrib.measure_mem_eq. It is the probabilistic prerequisite for monotonicity of the residual process d t-X_t.
-- source:
--   Avram Palmowski Pistorius (2007), bounded variation Lévy-Khintchine; canonical pinned SpectrallyNegativeLevy process definition and prior Proved support lemmas.

import Theorems.Thm_AvramDividend_Classical_bv_actual_levy_drift_upper_ae_fixed_time
import Mathlib.Probability.IdentDistrib
import Mathlib.MeasureTheory.OuterMeasure.AE

open AvramDividend.Classical MeasureTheory Set ProbabilityTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_actual_levy_drift_increment_ae_fixed_times
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (s t : ℝ≥0) (hst : s ≤ t) :
    ∀ᵐ ω ∂P,
      X.X t ω - X.X s ω ≤ ((t - s : ℝ≥0) : ℝ) * X.drift := by sorry
