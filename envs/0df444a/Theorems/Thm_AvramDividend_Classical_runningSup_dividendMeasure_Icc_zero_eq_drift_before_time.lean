-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Icc_zero_eq_drift_before_time
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_Icc_zero_eq_drift_before_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:26:38.425744+00:00
-- url     : https://prove2.me/theorems/24eeedfe-40df-4e60-8fe5-e77157d4f953
-- title:
--   Full closed interval dividend mass before a first jump has no boundary correction
-- statement:
--   If the true running supremum follows the drift line from time zero to nonnegative T, then the full Stieltjes dividend mass on the closed interval [0,T] equals dT. The initial point has no dividend atom, and the previously proved pathwise interval lemma handles (0,T]. This removes a subtle time-zero endpoint adjustment from the stopped first-jump reward.
-- source:
--   Prove2Me Proved runningSup_dividendMeasure_Ioc_eq_drift_before_time (e6c68384-783a-49a3-b850-072ee86ce85a); runningSup_dividendMeasure_zero_initial_atom (cbc76364-c2c0-4fb0-89a2-2de988872e43); Mathlib measure_sdiff_null.

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_before_time
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_initial_atom
import Mathlib.MeasureTheory.OuterMeasure.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_dividendMeasure_Icc_zero_eq_drift_before_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ)
    (hT : 0 ≤ T)
    (hPath : ∀ u : ℝ, 0 ≤ u → u ≤ T →
      runningSup X u.toNNReal ω = X.drift * u) :
    (dividendMeasure (runningSup X) ω) (Icc 0 T) =
      ENNReal.ofReal (X.drift * T) := by sorry
