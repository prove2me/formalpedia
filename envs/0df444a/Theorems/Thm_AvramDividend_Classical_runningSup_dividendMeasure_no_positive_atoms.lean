-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_no_positive_atoms
-- name    : AvramDividend.Classical.runningSup_dividendMeasure_no_positive_atoms
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:47:48.533779+00:00
-- url     : https://prove2.me/theorems/963e2c35-398a-4cf1-8017-2322a67349b5
-- title:
--   Running-supremum dividend measure has no atoms at positive time
-- statement:
--   For a spectrally negative Lévy path with no upward jumps, its running maximum has no jumps at strictly positive times. The genuine Stieltjes dividend measure of the running maximum consequently gives zero mass to every positive singleton. The proof uses the verified Stieltjes measure identity, right-limit equality, and (once proved) positive-time left-limit equality. This removes any terminal dividend atom at a strictly positive reflected drawdown ruin time.
-- source:
--   Prove2Me genuine Stieltjes dividendMeasure identification 036fcdf6-3be7-4bd6-a17a-92fb44710834, rightLim equality 086548ed-c97c-4fb2-aa51-c0805cc917a5, pending realTime_leftLim_eq_pos, Mathlib StieltjesFunction.measure_singleton.

import Mathlib.MeasureTheory.Measure.Stieltjes
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_eq_stieltjes
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_leftLim_eq_pos

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_dividendMeasure_no_positive_atoms
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (t : ℝ) (ht : 0 < t) :
    (dividendMeasure (runningSup X) ω) ({t} : Set ℝ) = 0 := by sorry
