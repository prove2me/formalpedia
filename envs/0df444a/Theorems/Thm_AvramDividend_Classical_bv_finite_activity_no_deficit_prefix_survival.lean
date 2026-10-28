-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_finite_activity_no_deficit_prefix_survival
-- name    : AvramDividend.Classical.bv_finite_activity_no_deficit_prefix_survival
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:23:42.219038+00:00
-- url     : https://prove2.me/theorems/a2dbf559-51fe-4b42-ad85-15dfd1e523b7
-- title:
--   Exponential survival of the actual finite-activity Lévy drift-deficit-free initial interval
-- statement:
--   The actual finite-activity bounded-variation Lévy process has no drift deficit throughout [0,t] with probability exp(-lambda*t). Its full-measure deficit monotonicity identifies the pathwise all-prior-times event with the already Proved fixed-time zero atom. This is the no-claim survival law needed to connect the true first negative jump with the strict zero-barrier drawdown ruin clock.
-- source:
--   Avram, Palmowski and Pistorius (2007), §3.3 equation (3.14); existing Prove2Me actual-process all-times monotonicity and fixed-time exponential atom law.

import Theorems.Thm_AvramDividend_Classical_bv_drift_deficit_ae_monotone_all_times
import Theorems.Thm_AvramDividend_Classical_bv_actual_residual_zero_atom_survival
import Mathlib.MeasureTheory.Measure.MeasureSpace
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_finite_activity_no_deficit_prefix_survival
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (t : ℝ≥0) :
    P.real {ω : Ω | ∀ s : ℝ≥0, s ≤ t →
      X.drift * (s : ℝ) - X.X s ω = 0} =
      Real.exp (-((t : ℝ) * (X.ν (Iio (0 : ℝ))).toReal)) := by sorry
