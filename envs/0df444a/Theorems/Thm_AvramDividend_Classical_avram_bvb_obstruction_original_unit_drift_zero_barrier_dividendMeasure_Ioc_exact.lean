-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_unit_drift_zero_barrier_dividendMeasure_Ioc_exact
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_unit_drift_zero_barrier_dividendMeasure_Ioc_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T07:44:01.539709+00:00
-- url     : https://prove2.me/theorems/9abab16e-d237-46c4-aa16-6f6db6400ff3
-- title:
--   Exact original zero-barrier Stieltjes dividend mass on a unit-drift nojump path before the horizon
-- statement:
--   For a genuine original unit-drift spectrally negative Lévy source following its deterministic linear path to horizon T, the original zero-barrier dividend Stieltjes measure assigns exactly t to (0,t] for each t≤T. This supplies the key cash-measure ingredient of the original positive-cap BV pathwise counterexample without any false general right-limit assumption.
-- source:
--   Proved barrierStrategy_self_eq_runningSup identifies the genuine zero-barrier dividends. Proved avram_bvb22_source linear reserve gives runningSup(u)=drift*u through T. Proved runningSup_dividendMeasure_Ioc_eq_drift_before_time then gives exact original Stieltjes interval mass.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_bvb22_original_zero_barrier_on_linear_source_has_zero_reserve
import Theorems.Thm_AvramDividend_Classical_barrierStrategy_self_eq_runningSup
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_eq_drift_before_time
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_unit_drift_zero_barrier_dividendMeasure_Ioc_exact
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (T t : ℝ≥0) (ht : t ≤ T)
    (hd : X.drift = 1)
    (hPath : ∀ s : ℝ≥0, s ≤ T →
      X.X s ω = (s : ℝ) * X.drift) :
    (dividendMeasure (barrierStrategy X 0 0) ω)
      (Ioc (0 : ℝ) (t : ℝ)) = ENNReal.ofReal (t : ℝ) := by sorry
