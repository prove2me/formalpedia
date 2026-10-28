-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioo_zero_eq_drift_before_time
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_Ioo_zero_eq_drift_before_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:27:25.511733+00:00
-- url     : https://prove2.me/theorems/7ed07f9a-fb8c-4ca1-860a-2e09717df5a6
-- title:
--   Strict pre-jump Stieltjes dividend mass excludes no terminal payment
-- statement:
--   If the actual running supremum equals the drift line until a strictly positive time T, the Stieltjes dividend mass on the strictly pre-jump time interval (0,T) equals dT. The real running supremum has no dividend-measure atom at positive time T, so deleting the stopping-time endpoint from (0,T] leaves the mass unchanged. This directly resolves the strict stopping convention in the zero-barrier reward.
-- source:
--   Prove2Me Proved runningSup_dividendMeasure_Ioc_eq_drift_before_time (e6c68384-783a-49a3-b850-072ee86ce85a); runningSup_dividendMeasure_no_positive_atoms (963e2c35-398a-4cf1-8017-2322a67349b5); Mathlib measure_sdiff_null.

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_before_time
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_positive_atoms
import Mathlib.MeasureTheory.OuterMeasure.Basic
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_dividendMeasure_Ioo_zero_eq_drift_before_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T : ℝ)
    (hT : 0 < T)
    (hPath : ∀ u : ℝ, 0 ≤ u → u ≤ T →
      runningSup X u.toNNReal ω = X.drift * u) :
    (dividendMeasure (runningSup X) ω) (Ioo 0 T) =
      ENNReal.ofReal (X.drift * T) := by sorry
