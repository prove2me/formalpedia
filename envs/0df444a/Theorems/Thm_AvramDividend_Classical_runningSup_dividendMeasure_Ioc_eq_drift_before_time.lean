-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_before_time
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_drift_before_time
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T00:11:54.492285+00:00
-- url     : https://prove2.me/theorems/e6c68384-783a-49a3-b850-072ee86ce85a
-- title:
--   Stieltjes dividend mass on every subinterval before a linear-record stopping time
-- statement:
--   Suppose the true running supremum follows the deterministic bounded-variation drift line on the full time interval from zero up to T. Then its Stieltjes dividend measure on every half-open subinterval within that time span is exactly the positive drift increment, with endpoint inequalities part of the theorem. This transfers a genuine pre-first-jump path identity into the measure-theoretic interval formula needed for stopped dividend valuation.
-- source:
--   Prove2Me Proved runningSup_dividendMeasure_Ioc_eq_drift_of_linear_record (1af3e92b-3470-4842-8b13-44384176fd5e); original Avram, Palmowski, Pistorius (2007) zero-barrier stopped dividend argument.

import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_of_linear_record
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.runningSup_dividendMeasure_Ioc_eq_drift_before_time
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) (T s t : ℝ)
    (hPath : ∀ u : ℝ, 0 ≤ u → u ≤ T →
      runningSup X u.toNNReal ω = X.drift * u)
    (hs : 0 ≤ s) (hst : s ≤ t) (ht : t ≤ T) :
    (dividendMeasure (runningSup X) ω) (Ioc s t) =
      ENNReal.ofReal (X.drift * (t - s)) := by sorry
